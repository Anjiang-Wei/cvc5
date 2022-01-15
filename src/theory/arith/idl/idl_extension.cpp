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
#include <deque>
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
  NodeManager *nm = NodeManager::currentNM();
  SkolemManager *sm = nm->getSkolemManager();
  shift_node = sm->mkSkolemFunction(SkolemFunId::NONE, nm->integerType(), 
    nm->mkConst(kind::CONST_RATIONAL, Rational(0)));
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
  /*
  for (size_t i = 0; i < d_numVars + 1; ++i) {
    d_matrix_new.emplace_back(d_numVars + 1);
    d_valid_new.emplace_back(d_numVars + 1, false);
  }
  */
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
  // if (debug) {
  //   std::cout << "IdlExtension::ppRewrite(): processing " << atom << std::endl;
  // }
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
    switch (atom.getKind()) {
      case kind::EQUAL: {
        // x = y: x - y <= 0 && y - x <= 0
        Node a_minus_b = nm->mkNode(kind::MINUS, atom[0], atom[1]);
        Node b_minus_a = nm->mkNode(kind::MINUS, atom[1], atom[0]);
        Node zero_const = nm->mkConstInt(0);
        Node ret = nm->mkNode(kind::AND,
            nm->mkNode(kind::LEQ, a_minus_b, zero_const),
            nm->mkNode(kind::LEQ, b_minus_a, zero_const));
        return ret;
      }
      case kind::LT: {
        // x < y: x - y <= -1
        Node a_minus_b = nm->mkNode(kind::MINUS, atom[0], atom[1]);
        Node ret = nm->mkNode(kind::LEQ, a_minus_b, nm->mkConstInt(-1));
        return ret;
      }
      case kind::LEQ: {
        // x <= y: x-y <= 0
        Node a_minus_b = nm->mkNode(kind::MINUS, atom[0], atom[1]);
        Node ret = nm->mkNode(kind::LEQ, a_minus_b, nm->mkConstInt(0));
        return ret;
      }
      case kind::GT: {
        // x > y: y-x <= -1
        Node b_minus_a = nm->mkNode(kind::MINUS, atom[1], atom[0]);
        Node ret = nm->mkNode(kind::LEQ, b_minus_a, nm->mkConstInt(-1));
        return ret;
      }
      case kind::GEQ: {
        // x >= y: y-x <= 0
        Node b_minus_a = nm->mkNode(kind::MINUS, atom[1], atom[0]);
        Node ret = nm->mkNode(kind::LEQ, b_minus_a, nm->mkConstInt(0));
        return ret;
      }
      default: break;
    }
    return ppRewrite(nm->mkNode(atom.getKind(), atom[0], atom[1]), lems);
  }
  else if (atom[0].getKind() == kind::VARIABLE && 
    atom[1].getKind() == kind::CONST_RATIONAL) {
    // handle (? x 5) ---> (? (- x shift_node) 5)
    Node x_shift = nm->mkNode(kind::MINUS, atom[0], shift_node);
    return ppRewrite(nm->mkNode(atom.getKind(), x_shift, atom[1]), lems);
  }
  else if (atom[0].getKind() == kind::PLUS && atom[1].getKind() == kind::PLUS) {
    // (op (+ x 22) (+ y 27))
    Node left = atom[0];
    Node right = atom[1];
    if (left[0].getKind() == kind::VARIABLE && left[1].getKind() == kind::CONST_RATIONAL
        && right[0].getKind() == kind::VARIABLE && right[1].getKind() == kind::CONST_RATIONAL) {
          Node const_minus = nm->mkConstInt(right[1].getConst<Rational>() - left[1].getConst<Rational>());
          Node var_minus = nm->mkNode(kind::MINUS, left[0], right[0]);
          return ppRewrite(nm->mkNode(atom.getKind(), var_minus, const_minus), lems);
    }
  }
  else if (atom[0].getKind() == kind::VARIABLE && atom[1].getKind() == kind::PLUS) {
    // (op x (+ y 22))
    Node left = atom[0];
    Node right = atom[1];
    if (right[0].getKind() == kind::VARIABLE && right[1].getKind() == kind::CONST_RATIONAL) {
          Node var_minus = nm->mkNode(kind::MINUS, left, right[0]);
          return ppRewrite(nm->mkNode(atom.getKind(), var_minus, right[1]), lems);
    }
  }
  else if (atom[0].getKind() == kind::PLUS && atom[1].getKind() == kind::CONST_RATIONAL) {
    // (op (+ x 15) 145)
    Node left = atom[0];
    Node right = atom[1];
    if (left[0].getKind() == kind::VARIABLE && left[1].getKind() == kind::CONST_RATIONAL) {
      Node const_minus = nm->mkConstInt(right.getConst<Rational>() - left[1].getConst<Rational>());
      return ppRewrite(nm->mkNode(atom.getKind(), left[0], const_minus), lems);
    }
  }
  else if (atom[0].getKind() == kind::MINUS && atom[1].getKind() == kind::CONST_RATIONAL) {
    // (op (- x 15) 145)
    Node left = atom[0];
    Node right = atom[1];
    if (left[0].getKind() == kind::VARIABLE && left[1].getKind() == kind::CONST_RATIONAL) {
      Node const_add = nm->mkConstInt(right.getConst<Rational>() + left[1].getConst<Rational>());
      return ppRewrite(nm->mkNode(atom.getKind(), left[0], const_add), lems);
    }
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
  Rational shift = Rational(0);
  if (d_varMap.count(shift_node)) {
    shift = distance[d_varMap[shift_node]];
    // std::cout << "shift = " << shift << std::endl;
  }

  for (size_t i = 0; i < d_numVars; i++)
  {
    distance[i] = dis[i] - shift;
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
  // if (debug) {
  //   std::cout << "processAssertion" << atom << std::endl;
  // }
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
      d_valid_new[i][j] = false;
    }
  }
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
  return false;
  /*
  for (size_t i = 0; i < d_numVars; i++) {
    d_dist_new.emplace_back(Rational(10000000));
  }
  d_dist_new.emplace_back(Rational(0));
  */
  /*
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
  */

  /*
  procedure Shortest-Path-Faster-Algorithm(G, s)
  1    for each vertex v ≠ s in V(G)
  2        d(v) := ∞
  3    d(s) := 0
  -----------------
  4    offer s into Q
  5    while Q is not empty
  6        u := poll Q
  7        for each edge (u, v) in E(G)
  8            if d(u) + w(u, v) < d(v) then
  9                d(v) := d(u) + w(u, v)
 10                if v is not in Q then
 11                    offer v into Q
  procedure Large-Label-Last(G, Q)
     x := average of d(v) for all v in Q
     while d(front(Q)) > x
         u := pop front of Q
         push u to back of Q
 */

/*
  Q.push_back(d_numVars);
  size_t Qsize = 1;
  size_t dsum = 0;
  while (!Q.empty()) {
    size_t u = Q.front();
    Q.pop_front();
    Qsize--;
    dsum = dsum - d_dist_new[u];
    for (size_t v = 0; v < d_numVars + 1; v++) {
      if (d_valid_new[u][v]) {
        if (d_dist_new[u] + d_matrix_new[u][v] < d_dist_new[v]) {
            d_dist_new[v] = d_dist_new[u] + d_matrix_new[u][v];
            if (std::find(Q.begin(), Q.end(), v) == Q.end()) {
              Q.push_back(v);
              Qsize++;
              dsum = dsum + d_dist_new[v];
              while (d_dist_new[Q.front()] * Qsize > dsum) {
                  size_t ufront = Q.front();
                  Q.pop_front();
                  Q.push_back(ufront);
              }
            }
          }
      }
    }
  }
  */
}

void IdlExtension::spfa_init() {
  for (int i = 0; i < (m_spfa >= 0 ? m_spfa + 2 : 0); i++) {
    adj[i].clear();
  }
  n_spfa = d_numVars;
  m_spfa = 0;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    for (size_t j = 0; j < d_numVars; ++j)
    {
      if (d_valid[i][j])
      {
        m_spfa++;
        // d_matrix_new[j][i] = d_matrix[i][j];
        // d_valid_new[j][i] = d_valid[i][j];
        adj[j].emplace_back(i, d_matrix[i][j]);
      }
    }
  }

}
bool IdlExtension::spfa_early_terminate()
{

   /* There are d_numVars+1 vertices in total
    [0, d_numVars) are original matrix, d_numVars is the additional one */
  // https://konaeakira.github.io/assets/code-snippets/cycle-detection-with-spfa.cpp
  for (int i = 0; i < n_spfa; i++) {
    dis.emplace_back(Rational(0));
  }
  // std::fill(dis, dis + n_spfa, 0);
	std::fill(pre, pre + n_spfa, -1);
	std::fill(in_queue, in_queue + n_spfa, true);
  Rational sum(0);
  num_on_stack = 0;
	for (int i = 0; i < n_spfa; ++i)
  {
		queue.push_back(i);
    num_on_stack++;
  }
  int iter = 0;
	while (!queue.empty())
	{
		int u = queue.front();
		queue.pop_front();
    num_on_stack--;
    sum = sum - dis[u];
		in_queue[u] = false;
		for (auto [v, w] : adj[u])
    {
			if (dis[u] + w < dis[v])
			{
				pre[v] = u;
				dis[v] = dis[u] + w;
				if (++iter == n_spfa)
        {
            iter = 0;
            if (detect_cycle())
                return true;
        }
				if (!in_queue[v])
				{
					queue.push_back(v);
					in_queue[v] = true;
          num_on_stack++;
          sum = sum + dis[v];
          while (dis[queue.front()] * num_on_stack > sum) {
              int ufront = queue.front();
              queue.pop_front();
              queue.push_back(ufront);
          }
				}
			}
    }

	}
  if (detect_cycle())
    return true;
	return false;
}


bool IdlExtension::detect_cycle()
{
    std::vector<int> vec;
    std::fill(on_stack, on_stack + n_spfa, false);
    std::fill(visited, visited + n_spfa, false);
    for (int i = 0; i < n_spfa; ++i)
        if (!visited[i])
        {
            for (int j = i; j != -1; j = pre[j])
                if (!visited[j])
                {
                    visited[j] = true;
                    vec.push_back(j);
                    on_stack[j] = true;
                }
                else
                {
                    if (on_stack[j])
                        return true;
                    break;
                }
            for (int j : vec)
                on_stack[j] = false;
            vec.clear();
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
  // init_new_matrix();

  spfa_init();
  
  // printMatrix(d_matrix_new, d_valid_new, d_numVars + 1);
  //bool result = Bellman_Ford(d_matrix_new, d_valid_new, d_numVars);
  bool result = spfa_early_terminate();
  
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
      if (d_varList[j] == shift_node) {
        std::cout << std::setw(6) << "shift";
      } else {
        std::cout << std::setw(6) << d_varList[j];
      }
    }
    else {
      std::cout << std::setw(6) << "***";
    }
  }
  std::cout << std::endl;
  for (size_t i = 0; i < d_numVars; ++i)
  {
    if (i < d_varList.size()) {
      if (d_varList[i] == shift_node) {
        std::cout << std::setw(6) << "shift";
      } else {
        std::cout << std::setw(6) << d_varList[i];
      }
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
