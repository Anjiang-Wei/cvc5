/*********************                                                        */
/*! \file worker.h
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

#ifndef CVC4__SMT__E_SOLVER__WORKER_H
#define CVC4__SMT__E_SOLVER__WORKER_H

#include <unordered_map>

#include "expr/expr_manager.h"
#include "expr/node.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/e_solver/thread_pool.h"
#include "smt/e_solver/var_map.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace smt {

struct Worker;

struct JobOutput
{
  Worker* d_worker;
  Instantiator* d_instantiator;
  std::vector<Node> d_toAssert;
  bool d_done;

  JobOutput();

  JobOutput(Worker* worker,
            Instantiator* instantiator,
            const std::vector<Node>& toAssert,
            bool done);
  JobOutput(const JobOutput& other);
  JobOutput& operator=(const JobOutput& other);

  void clear();

  ~JobOutput();
};

struct Worker
{
  Worker(size_t id, NodeManager* mainNm, const LogicInfo& logic)
      : d_pool(nullptr),
        d_id(id),
        d_mainNm(mainNm),
        d_logic(logic),
        d_em(new ExprManager()),
        d_interEm(new ExprManager()),
        d_interNm(d_interEm->getNodeManager()),
        d_smt(new SmtEngine(d_em->getNodeManager())),
        d_vmMainInter(d_mainNm, d_interNm),
        d_vmInterWorker(d_interNm, d_em->getNodeManager()),
        d_timeout(1000),
        d_ready(true)
  {
    initSolver();
  }

  ~Worker()
  {
    {
      NodeManagerScope nms(d_interNm);
      d_abstractAssertsBuffer.clear();
    }

    NodeManagerScope nms(getNodeManager());
    d_abstractAsserts.clear();
  }

  void initSolver()
  {
    d_smt->setIsInternalSubsolver();
    d_smt->setLogic(d_logic);
    d_smt->getOptions().set(options::produceModels, true);
    d_smt->getOptions().set(options::fullSaturateQuant, true);
  }

  NodeManager* getNodeManager() { return d_em->getNodeManager(); }

  void getLiterals(std::unordered_set<Node, NodeHashFunction>& literals, Node n)
  {
    std::unordered_set<Node, NodeHashFunction> visited;
    std::vector<Node> toVisit{n};
    while (!toVisit.empty())
    {
      Node curr = toVisit.back();
      toVisit.pop_back();

      if (visited.find(curr) != visited.end())
      {
        continue;
      }
      visited.insert(curr);

      if (curr.getType().isBoolean()
          && (curr.getNumChildren() == 0 || !curr[0].getType().isBoolean()))
      {
        Trace("e-solver-debug") << "Get value of " << curr << std::endl;
        Node val = d_smt->getValue(curr);
        literals.insert(val.getConst<bool>() ? curr : curr.notNode());
        continue;
      }

      toVisit.emplace_back(curr);
      if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        toVisit.push_back(curr.getOperator());
      }
      toVisit.insert(toVisit.end(), curr.begin(), curr.end());
    }
  }

  void reinit()
  {
    // d_timeout *= 2;
    d_smt.reset(new SmtEngine(getNodeManager()));
    initSolver();

    for (const Node& a : d_abstractAsserts)
    {
      d_smt->assertFormula(a);
    }

    d_smt->setOutOfResourcesCallback(
        [this]() { return this->d_pool->stopped(); });
  }

  ThreadPool<Worker, JobOutput>* d_pool;
  size_t d_id;
  NodeManager* d_mainNm;
  LogicInfo d_logic;
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<ExprManager> d_interEm;
  NodeManager* d_interNm;
  std::unique_ptr<SmtEngine> d_smt;
  std::vector<Node> d_abstractAsserts;
  std::mutex d_abstractAssertsBufferMut;
  std::condition_variable d_abstractAssertsBufferCv;
  std::vector<Node> d_abstractAssertsBuffer;
  VarMap d_vmMainInter;
  VarMap d_vmInterWorker;
  unsigned long d_timeout;
  bool d_ready;
};

}  // namespace smt
}  // namespace CVC4

#endif
