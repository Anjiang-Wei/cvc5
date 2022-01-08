/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * IDL extension.
 */

#include "theory/arith/idl/idl_extension.h"

#include <iomanip>
#include <queue>
#include <set>

#include "expr/node_builder.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace idl {

IdlExtension::IdlExtension(Env& env, TheoryArith& parent)
    : EnvObj(env),
      d_parent(parent),
      d_varMap(context()),
      d_varList(context()),
      d_facts(context()),
      d_numVars(0)
{
}

void IdlExtension::preRegisterTerm(TNode node)
{
  Assert(d_numVars == 0);
  if (node.isVar())
  {
    Trace("theory::arith::idl")
        << "IdlExtension::preRegisterTerm(): processing var " << node
        << std::endl;
    unsigned size = d_varMap.size();
    d_varMap[node] = size;
    d_varList.push_back(node);
  }
}

void IdlExtension::presolve()
{
  d_numVars = d_varMap.size();
  Trace("theory::arith::idl")
      << "IdlExtension::preSolve(): d_numVars = " << d_numVars << std::endl;

  // Initialize adjacency matrix.
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_matrix.emplace_back(d_numVars);
    d_valid.emplace_back(d_numVars, false);
  }

  //david
  for (size_t i = 0; i < d_numVars + 1; ++i) {
    d_matrix_new.emplace_back(d_numVars + 1);
    d_valid_new.emplace_back(d_numVars + 1, false);
  }
}

void IdlExtension::notifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("theory::arith::idl")
      << "IdlExtension::notifyFact(): processing " << fact << std::endl;
  d_facts.push_back(fact);
}

Node IdlExtension::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  // We are only interested in predicates
  if (!atom.getType().isBoolean())
  {
    return atom;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  // std::cout << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  if (atom[0].getKind() == kind::CONST_RATIONAL)
  {
    // Move constant value to right-hand side
    Kind k = kind::EQUAL;
    switch (atom.getKind())
    {
      // -------------------------------------------------------------------------
      // TODO: Handle these cases.
      // -------------------------------------------------------------------------
      case kind::EQUAL:
      {
        return ppRewrite(nm->mkNode(kind::EQUAL, atom[1], atom[0]), lems);
      }
      case kind::LT:
      {
        return ppRewrite(nm->mkNode(kind::GT, atom[1], atom[0]), lems);
      }
      case kind::LEQ:
      {
        return ppRewrite(nm->mkNode(kind::GEQ, atom[1], atom[0]), lems);
      }
      case kind::GT:
      {
        return ppRewrite(nm->mkNode(kind::LT, atom[1], atom[0]), lems);
      }
      case kind::GEQ:
      {
        return ppRewrite(nm->mkNode(kind::LEQ, atom[1], atom[0]), lems);
      }
      default: break;
    }
    return ppRewrite(nm->mkNode(k, atom[1], atom[0]), lems);
  }
  else if (atom[1].getKind() == kind::VARIABLE)
  {
    // Handle the case where there are no constants, e.g., (= x y) where both
    // x and y are variables
    // -------------------------------------------------------------------------
    // TODO: Handle this case.
    // -------------------------------------------------------------------------
    Node a_minus_b = nm->mkNode(kind::MINUS, atom[0], atom[1]);
    Node zero_const = nm->mkConstInt(0);
    Node ret = nm->mkNode(atom.getKind(), a_minus_b, zero_const);
    return ppRewrite(ret, lems);
  }

  switch (atom.getKind())
  {
    case kind::EQUAL:
    {
      Node l_le_r = nm->mkNode(kind::LEQ, atom[0], atom[1]);
      Assert(atom[0].getKind() == kind::MINUS);
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right);
      Node r_le_l = nm->mkNode(kind::LEQ, negated_left, negated_right);
      // std::cout << "case equal, tranform to " << nm->mkNode(kind::AND, l_le_r, r_le_l) << std::endl;
      return nm->mkNode(kind::AND, l_le_r, r_le_l);
    }

    // -------------------------------------------------------------------------
    // TODO: Handle these cases.
    // -------------------------------------------------------------------------
    case kind::LT:
    {
      const Rational& right = atom[1].getConst<Rational>();
      Node right_minus_1 = nm->mkConstInt(right - 1);
      // std::cout << "case lt, tranform to " << nm->mkNode(kind::LEQ, atom[0], right_minus_1) << std::endl;
      return nm->mkNode(kind::LEQ, atom[0], right_minus_1);
    }
    case kind::LEQ:
    {
      break;
    }
    case kind::GT:
    {
      Assert(atom[0].getKind() == kind::MINUS);
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right - 1);
      // std::cout << "case gt, tranform to " << nm->mkNode(kind::LEQ, negated_left, negated_right) << std::endl;
      return nm->mkNode(kind::LEQ, negated_left, negated_right);
    }
    case kind::GEQ:
    {
      Assert(atom[0].getKind() == kind::MINUS);
      Node negated_left = nm->mkNode(kind::MINUS, atom[0][1], atom[0][0]);
      const Rational& right = atom[1].getConst<Rational>();
      Node negated_right = nm->mkConstInt(-right);
      // std::cout << "case geq, tranform to " << nm->mkNode(kind::LEQ, negated_left, negated_right) << std::endl;
      return nm->mkNode(kind::LEQ, negated_left, negated_right);
    }

    default: break;
  }
  return atom;
}

void IdlExtension::postCheck(Theory::Effort level)
{
  if (!Theory::fullEffort(level))
  {
    return;
  }

  Trace("theory::arith::idl")
      << "IdlExtension::postCheck(): number of facts = " << d_facts.size()
      << std::endl;

  // Reset the graph
  for (size_t i = 0; i < d_numVars; i++)
  {
    for (size_t j = 0; j < d_numVars; j++)
    {
      d_valid[i][j] = false;
    }
  }

  for (Node fact : d_facts)
  {
    // For simplicity, we reprocess all the literals that have been asserted to
    // this theory solver. A better implementation would process facts in
    // notifyFact().
    Trace("theory::arith::idl")
        << "IdlExtension::check(): processing " << fact << std::endl;
    // std::cout << "IdlExtension::check(): processing " << fact << std::endl;
    processAssertion(fact);
  }

  if (negativeCycle())
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    NodeBuilder conjunction(kind::AND);
    for (Node fact : d_facts)
    {
      conjunction << fact;
    }
    Node conflict = conjunction;
    // Send the conflict using the inference manager. Each conflict is assigned
    // an ID. Here, we use  ARITH_CONF_IDL_EXT, which indicates a generic
    // conflict detected by this extension
    d_parent.getInferenceManager().conflict(conflict,
                                            InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }
}

bool IdlExtension::collectModelInfo(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  std::vector<Rational> distance(d_numVars, Rational(0));

  // ---------------------------------------------------------------------------
  // TODO: implement model generation by computing the single-source shortest
  // path from a node that has distance zero to all other nodes
  // ---------------------------------------------------------------------------
  for (size_t i = 0; i < d_numVars; i++)
  {
    distance[i] = d_dist_new[i];
  }

  NodeManager* nm = NodeManager::currentNM();
  for (size_t i = 0; i < d_numVars; i++)
  {
    // Assert that the variable's value is equal to its distance in the model
    m->assertEquality(d_varList[i], nm->mkConstInt(distance[i]), true);
  }

  return true;
}

void IdlExtension::processAssertion(TNode assertion)
{
  bool polarity = assertion.getKind() != kind::NOT;
  TNode atom = polarity ? assertion : assertion[0];
  Assert(atom.getKind() == kind::LEQ);
  Assert(atom[0].getKind() == kind::MINUS);
  TNode var1 = atom[0][0];
  TNode var2 = atom[0][1];

  Rational value = (atom[1].getKind() == kind::UMINUS)
                       ? -atom[1][0].getConst<Rational>()
                       : atom[1].getConst<Rational>();

  if (!polarity)
  {
    std::swap(var1, var2);
    value = -value - Rational(1);
  }

  size_t index1 = d_varMap[var1];
  size_t index2 = d_varMap[var2];

  if (!d_valid[index1][index2] || value < d_matrix[index1][index2])
  {
    d_valid[index1][index2] = true;
    d_matrix[index1][index2] = value;
  }
}

void IdlExtension::init_new_matrix()
{
  for (size_t i = 0; i < d_numVars; ++i)
  {
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (d_valid[i][j])
      {
        d_matrix_new[j][i] = d_matrix[i][j];
        d_valid_new[j][i] = d_valid[i][j];
      }
    }
  }
  for (size_t i = 0; i < d_numVars; ++i)
  {
    d_matrix_new[d_numVars][i] = 0;
    d_valid_new[d_numVars][i] = true;
  }
}

bool IdlExtension::Bellman_Ford(const std::vector<std::vector<Rational>> d_matrix_new,
                  const std::vector<std::vector<bool>> d_valid_new,
                  const size_t d_numVars)
{
  /* There are d_numVars+1 vertices in total
    [0, d_numVars) are original matrix, d_numVars is the additional one */
  for (size_t i = 0; i < d_numVars; i++) {
    d_dist_new.emplace_back(Rational(10000000));
  }
  d_dist_new.emplace_back(Rational(0));
  for (size_t i = 0; i < d_numVars; i++) { // repeat d_numVars (|V| - 1) times
    for (size_t u = 0; u < d_numVars + 1; u++) {
      for (size_t v = 0; v < d_numVars + 1; v++) {
        if (d_valid_new[u][v]) {
          if (d_dist_new[u] + d_matrix_new[u][v] < d_dist_new[v]) {
            d_dist_new[v] = d_dist_new[u] + d_matrix_new[u][v];
          }
        }
      }
    }
  }

  for (size_t u = 0; u < d_numVars + 1; u++) {
      for (size_t v = 0; v < d_numVars + 1; v++) {
        if (d_valid_new[u][v]) {
          if (d_dist_new[u] + d_matrix_new[u][v] < d_dist_new[v]) {
            return true;
          }
        }
      }
    }
  return false;
}

bool IdlExtension::negativeCycle()
{
  // --------------------------------------------------------------------------
  // TODO: write the code to detect a negative cycle.
  // --------------------------------------------------------------------------
  // std::cout << "Enter negativeCycle2" << std::endl;
  // printMatrix(d_matrix, d_valid, d_numVars);
  //david
  init_new_matrix();
  
  // printMatrix(d_matrix_new, d_valid_new, d_numVars + 1);
  bool result = Bellman_Ford(d_matrix_new, d_valid_new, d_numVars);
  
  return result;
}

void IdlExtension::printMatrix(const std::vector<std::vector<Rational>>& matrix,
                               const std::vector<std::vector<bool>>& valid,
                               const size_t d_numVars)
{
  std::cout << "      ";
  for (size_t j = 0; j < d_numVars; ++j)
  {
    if (j < d_varList.size()) {
      std::cout << std::setw(6) << d_varList[j];
    }
    else {
      std::cout << std::setw(6) << "***";
    }
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    if (i < d_varList.size()) {
      std::cout << std::setw(6) << d_varList[i];
    }
    else {
      std::cout << std::setw(6) << "***";
    }
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (valid[i][j])
      {
        std::cout << std::setw(6) << matrix[i][j];
      }
      else
      {
        std::cout << std::setw(6) << "oo";
      }
    }
    std::cout << std::endl;
  }
}

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
