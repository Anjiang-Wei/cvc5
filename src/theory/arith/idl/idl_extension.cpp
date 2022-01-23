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
      d_numVars(0),
      pre_detect_cycle(context())
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
  pre = (size_t*) malloc(sizeof(size_t) * d_numVars);
  in_queue = (bool*) malloc(sizeof(bool) * d_numVars);
  visited = (bool*) malloc(sizeof(bool) * d_numVars);
  on_stack = (bool*) malloc(sizeof(bool) * d_numVars);
  myfacts = (int**) malloc(sizeof(int*) * d_numVars);
  myvalues = (long long**) malloc(sizeof(long long*) * d_numVars);
  adj = (std::vector<std::pair<size_t, Rational>>**)
    malloc(sizeof(std::vector<std::pair<size_t, Rational>>*) * d_numVars);
  for (int i = 0; i < d_numVars; i++) {
    adj[i] = new std::vector<std::pair<size_t, Rational>>();
    myfacts[i] = (int*) malloc(sizeof(int) * d_numVars);
    myvalues[i] = (long long*) malloc(sizeof(long long) * d_numVars);
  }
}

IdlExtension::~IdlExtension() {
  free(pre);
  free(in_queue);
  free(visited);
  free(on_stack);
  for (int i = 0; i < d_numVars; i++) {
    delete adj[i];
    free(myfacts[i]);
    free(myvalues[i]);
  }
  free(adj);
  free(myfacts);
  free(myvalues);
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
  // if (true) {
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


  for (int i = 0; i < d_numVars; i++) {
    adj[i]->clear();
  }
  n_spfa = d_numVars;
  m_spfa = 0;

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
  if (pre_detect_cycle.size() > 0) {
    d_parent.getInferenceManager().conflict(pre_detect_cycle[0],
              InferenceId::ARITH_CONF_IDL_EXT);
    return;
  }

  auto result = spfa_early_terminate();
  if (result.size() > 0)
  {
    // Return a conflict that includes all the literals that have been asserted
    // to this theory solver. A better implementation would only include the
    // literals involved in the conflict here.
    if (result.size() == 1) {
        d_parent.getInferenceManager().conflict(result[0],
                                            InferenceId::ARITH_CONF_IDL_EXT);
        return;
    }
    NodeBuilder conjunction(kind::AND);
    for (Node fact : result)
    {
      conjunction << fact;
    }
    // std::cout << "end reporting" << std::endl;
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
  // if (true) {
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

  if (index1 == index2) {
    if (value < Rational(0)) { // already a negative cycle
      pre_detect_cycle.push_back(assertion);
      return;
    }
  }

  adj[index2]->emplace_back(index1, value);
  myfacts[index2][index1] = m_spfa;
  myvalues[index2][index1] = (long long) value.getDouble();
  m_spfa++;
}


std::vector<TNode> IdlExtension::spfa_early_terminate()
{

   /* There are d_numVars+1 vertices in total
    [0, d_numVars) are original matrix, d_numVars is the additional one */
  // https://konaeakira.github.io/assets/code-snippets/cycle-detection-with-spfa.cpp
  std::vector<TNode> result;
  if (dis.size() == 0) {
    for (int i = 0; i < n_spfa; i++) {
      dis.emplace_back(Rational(0));
    }
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
		for (auto [v, w] : *(adj[u]))
    {
			if (dis[u] + w < dis[v])
			{
				pre[v] = u;
				dis[v] = dis[u] + w;
				if (++iter == n_spfa)
        {
            iter = 0;
            result = detect_cycle();
            if (result.size() > 0)
                return result;
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
  result = detect_cycle();
  return result;
}


std::vector<TNode> IdlExtension::detect_cycle()
{
    std::vector<int> vec;
    std::vector<TNode> result;
    std::fill(on_stack, on_stack + n_spfa, false);
    std::fill(visited, visited + n_spfa, false);
    for (int i = 0; i < n_spfa; ++i)
    {
        if (!visited[i])
        {
            for (int j = i; j != -1; j = pre[j])
            {
                if (!visited[j])
                {
                    visited[j] = true;
                    vec.push_back(j);
                    on_stack[j] = true;
                }
                else
                {
                    if (on_stack[j])
                    {
                        long long sum_cycle = 0;
                        int current = j;
                        while (pre[current] != j) {
                          result.emplace_back(d_facts[myfacts[pre[current]][current]]);
                          sum_cycle = sum_cycle + myvalues[pre[current]][current];
                          current = pre[current];
                        }
                        result.emplace_back(d_facts[myfacts[pre[current]][current]]);
                        sum_cycle = sum_cycle + myvalues[pre[current]][current];
                        if (sum_cycle < 0) {
                            return result;
                        }
                        else {
                          result.clear();
                            break;
                        }
                    }
                    break;
                }
            }
            for (int j : vec)
            {
                on_stack[j] = false;
            }
            vec.clear();
        }
    }
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
