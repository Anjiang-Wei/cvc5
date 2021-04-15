/*********************                                                        */
/*! \file e_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A CEGAR solver for quantifiers
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__E_SOLVER__E_SOLVER_H
#define CVC4__SMT__E_SOLVER__E_SOLVER_H

#include <unordered_map>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/smt_engine_state.h"
#include "util/result.h"

namespace CVC4 {
namespace smt {

class ESolver
{
 public:
  ESolver(SmtEngine* parent, SmtEngineState* state);
  ~ESolver();

  /** Check satisfiability using the e-solver */
  Result checkSatisfiability(Assertions& asserts);

 private:
  /** Check if the formula f is satisfiable */
  Result isUnsat(Node f);

  /**
   * Abstract the original formula. This method removes quantifiers and
   * replaces bound variables with fresh constants that represent abstracted
   * e-terms.
   *
   * @param n Node to abstract
   * @param cache A cache that maps terms to their abstractions
   * @param eMap Maps abstracted literals to the e-term bodies
   * @return The abstracted version of n
   */
  Node abstract(Node n,
                std::unordered_map<Node, Node, NodeHashFunction>& cache,
                std::map<std::vector<Node>, std::pair<Node, Node>>& eMap);

  void apps(Node f, Node n, std::vector<Node>& result);

  bool hasTVar(Node t, Node n);

  /** The parent SMT engine */
  SmtEngine* d_parent;
  SmtEngineState* d_state;

  TimerStat d_eSolverTime;
  TimerStat d_mainSolverTime;
  TimerStat d_mainWaitTime;
  IntStat d_numMainChecks;
  IntStat d_numAxioms;
  IntStat d_numRounds;
};

Node mapConsts(Node n, std::unordered_map<Node, Node, NodeHashFunction>& cache);

/** Combines nested quantifiers */
Node collapseQuantifiers(Node f);
Node additionalLemmas(Node inst);

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__E_SOLVER_H */
