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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H
#define CVC5__THEORY__ARITH__IDL__IDL_EXTENSION_H

#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/skolem_lemma.h"
#include "theory/theory.h"
#include "theory/theory_model.h"
#include <deque>
#include <unordered_map>
#include <boost/functional/hash.hpp>

namespace cvc5 {
namespace theory {
namespace arith {

class TheoryArith;

namespace idl {

/**
 * Handles integer difference logic (IDL) constraints.
 */
class IdlExtension : protected EnvObj
{
 public:
  IdlExtension(Env& env, TheoryArith& parent);
  ~IdlExtension();

  /** Register a term that is in the formula */
  void preRegisterTerm(TNode);

  /** Set up the solving data structures */
  void presolve();

  /** Called for each asserted literal */
  void notifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal);

  /** Pre-processing of input atoms */
  Node ppRewrite(TNode atom, std::vector<SkolemLemma>& lems);

  /** Check for conflicts in the current facts */
  void postCheck(Theory::Effort level);

  /** Get all information regarding the current model */
  bool collectModelInfo(TheoryModel* m, const std::set<Node>& termSet);

 private:
  /** Process a new assertion */
  void processAssertion(TNode assertion);

  /** Return true iff the graph has a negative cycle */
  // bool negativeCycle();

  /** Print the matrix */
  void printMatrix(const std::vector<std::vector<Rational>>& matrix,
                   const std::vector<std::vector<bool>>& valid,
                   const size_t d_numVars);
  
  // void init_new_matrix();

  // bool Bellman_Ford(const std::vector<std::vector<Rational>> d_matrix_new,
  //                   const std::vector<std::vector<bool>> d_valid_new,
  //                   const size_t d_numVars);

  typedef context::CDHashMap<TNode, size_t> TNodeToUnsignedCDMap;

  /** The owner of this extension */
  TheoryArith& d_parent;

  /** Map from variables to the first element of their list */
  TNodeToUnsignedCDMap d_varMap;

  /** Context-dependent vector of variables */
  context::CDList<TNode> d_varList;

  /** Context-dependent list of asserted theory literals */
  context::CDList<TNode> d_facts;

  /** Number of variables in the graph */
  size_t d_numVars;

  Node shift_node;

  //const int MAX_N = 1000000;

  int n_spfa, m_spfa;
  std::vector<std::pair<size_t, Rational>>** adj;
  int** myfacts;
  long long** myvalues;

  std::vector<Rational> dis;
  size_t* pre;
  bool* in_queue;

  bool* visited;
  bool* on_stack;
  std::vector<TNode> detect_cycle();
  std::vector<TNode> spfa_early_terminate();
  void spfa_init();
  int num_on_stack;
  std::deque<int> queue;

  context::CDList<TNode> pre_detect_cycle;

  // bool debug = false;
}; /* class IdlExtension */

}  // namespace idl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif