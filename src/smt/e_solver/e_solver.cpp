/*********************                                                        */
/*! \file e_solver.cpp
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

#include "smt/e_solver/e_solver.h"

#include <chrono>
#include <condition_variable>
#include <future>
#include <mutex>
#include <thread>

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/e_solver/thread_pool.h"
#include "smt/e_solver/worker.h"
#include "smt/model.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/cegqi/vts_term_cache.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {
namespace smt {

using namespace CVC4::theory;

struct Instantiator
{
  NodeManager* d_mainNm;
  std::vector<TNode> d_key;
  unsigned long d_timeout;
  bool d_assertFunctionModels;
  TNode d_cube;
  TNode d_eBody;

  Instantiator(NodeManager* mainNm, const LogicInfo& logic)
      : d_mainNm(mainNm), d_timeout(1000), d_assertFunctionModels(false)
  {
  }

  ~Instantiator() {}
};

ESolver::ESolver(SmtEngine* parent, SmtEngineState* state)
    : d_parent(parent),
      d_state(state),
      d_eSolverTime("smt::eSolver::time"),
      d_mainSolverTime("smt::eSolver::mainSolverTime"),
      d_mainWaitTime("smt::eSolver::mainWaitTime"),
      d_numMainChecks("smt::eSolver::numMainChecks", 0),
      d_numAxioms("smt::eSolver::numAxioms", 0),
      d_numRounds("smt::eSolver::numRounds", 0)
{
  Trace("e-solver") << "Using e-solver" << std::endl;
  smtStatisticsRegistry()->registerStat(&d_eSolverTime);
  smtStatisticsRegistry()->registerStat(&d_mainSolverTime);
  smtStatisticsRegistry()->registerStat(&d_mainWaitTime);
  smtStatisticsRegistry()->registerStat(&d_numMainChecks);
  smtStatisticsRegistry()->registerStat(&d_numAxioms);
  smtStatisticsRegistry()->registerStat(&d_numRounds);
}

ESolver::~ESolver()
{
  SmtScope smts(d_parent);
  smtStatisticsRegistry()->unregisterStat(&d_eSolverTime);
  smtStatisticsRegistry()->unregisterStat(&d_mainSolverTime);
  smtStatisticsRegistry()->unregisterStat(&d_mainWaitTime);
  smtStatisticsRegistry()->unregisterStat(&d_numMainChecks);
  smtStatisticsRegistry()->unregisterStat(&d_numAxioms);
  smtStatisticsRegistry()->unregisterStat(&d_numRounds);
}

Result ESolver::checkSatisfiability(Assertions& asserts)
{
  d_state->notifyCheckSat(false);

  NodeManager* nm = NodeManager::currentNM();
  preprocessing::AssertionPipeline ap = asserts.getAssertionPipeline();
  std::vector<Node> as(ap.begin(), ap.end());
  Node f = as.size() == 0
               ? nm->mkConst(true)
               : (as.size() == 1 ? as[0] : nm->mkNode(kind::AND, as));

  Trace("e-solver") << "Original input " << f << std::endl;
  f = collapseQuantifiers(f);
  Trace("e-solver") << "Preprocessed input " << f << std::endl;

  Result r = isUnsat(f);
  if (r.isSat() == Result::SAT_UNKNOWN)
  {
    Trace("e-solver") << std::endl;
    Trace("e-solver") << "Could not prove `unsat`, trying to prove `sat`..."
                      << std::endl;
    r = isUnsat(f.notNode());
    if (r.isSat() == Result::UNSAT)
    {
      r = Result(Result::SAT);
    }
  }
  d_state->notifyCheckSatResult(false, r);
  return r;
}

std::pair<bool, JobOutput> refine(Worker* worker, Instantiator* instantiator)
{
  SmtEngine* smt = worker->d_smt.get();
  NodeManager* nm = worker->getNodeManager();
  SmtScope smts(smt);

  bool timedOut = false;
  std::vector<Node> toAssert;

  {
    Trace("e-solver") << "Worker updating assertions..." << std::endl;
    std::vector<Node>& abstractAsserts = worker->d_abstractAsserts;
    {
      std::unique_lock<std::mutex> lock(worker->d_abstractAssertsBufferMut);
      worker->d_abstractAssertsBufferCv.wait(lock, [worker] {
        return worker->d_ready || worker->d_pool->stopped();
      });
      if (worker->d_pool->stopped())
      {
        Trace("e-solver") << "Thread pool stopped, shutting down" << std::endl;

        lock.unlock();
        return std::make_pair(true, JobOutput(worker, instantiator, {}, true));
      }
      for (const Node& am : worker->d_abstractAssertsBuffer)
      {
        Node a = worker->d_vmInterWorker.importNode(am);
        Trace("e-solver") << "Asserting " << a << " to worker" << std::endl;
        smt->assertFormula(a);
        abstractAsserts.emplace_back(a);
      }
      {
        NodeManagerScope nms(worker->d_interNm);
        worker->d_abstractAssertsBuffer.clear();
      }
    }

    smt->push();

    Node cube;
    {
      NodeManagerScope nmsInter(worker->d_interNm);
      Node cubeInter = worker->d_vmMainInter.importNode(instantiator->d_cube);
      {
        NodeManagerScope nmsWorker(worker->getNodeManager());
        cube = worker->d_vmInterWorker.importNode(cubeInter);
      }
    }

    Trace("e-solver") << "Asserting cube " << cube << std::endl;
    smt->assertFormula(cube.notNode());

    Trace("e-solver") << "Instantiator checking assertions... ";
    Result r = smt->checkSat();
    Trace("e-solver") << r << std::endl;
    if (r.isUnknown() && r.whyUnknown() == Result::TIMEOUT)
    {
      worker->reinit();
      return std::make_pair(false, JobOutput(worker, instantiator, {}, false));
    }
    else if (r.isSat() == Result::UNSAT
             || (r.isUnknown() && (r.whyUnknown() == Result::INTERRUPTED)))
    {
      // Nothing more to learn from this instantiator
      Trace("e-solver") << "Instantiator done";
      smt->pop();
      return std::make_pair(true, JobOutput(worker, instantiator, {}, true));
    }

    // Gather SAT assignment
    std::unordered_set<Node, NodeHashFunction> literals;
    std::unordered_set<Node, NodeHashFunction> asyms;
    for (const Node& a : abstractAsserts)
    {
      worker->getLiterals(literals, a);
      expr::getSymbols(a, asyms);
    }
    Trace("e-solver") << "SAT assignment = " << literals << std::endl;

    // Gather function models
    std::unordered_map<Node, Node, NodeHashFunction> cache;
    std::unordered_map<Node, Node, NodeHashFunction> fmodels;
    for (const Node& asym : asyms)
    {
      Node val = mapConsts(smt->getValue(asym), cache);
      fmodels[asym] = val;
    }

    std::vector<Node> axioms;
    bool useSygus = false;
    std::vector<Node> ts;
    for (const TNode& t : instantiator->d_key)
    {
      NodeManagerScope nmsInter(worker->d_interNm);
      Node tInter = worker->d_vmMainInter.importNode(t);
      {
        NodeManagerScope nmsWorker(worker->getNodeManager());
        ts.emplace_back(worker->d_vmInterWorker.importNode(tInter));
      }
    }
    Node eBody;
    {
      NodeManagerScope nmsInter(worker->d_interNm);
      Node eBodyInter = worker->d_vmMainInter.importNode(instantiator->d_eBody);
      {
        NodeManagerScope nmsWorker(worker->getNodeManager());
        eBody = worker->d_vmInterWorker.importNode(eBodyInter);
      }
    }
    Trace("e-solver") << "Body = " << eBody << std::endl;

    std::vector<Node> tvs;
    for (const Node& t : ts)
    {
      if (t.getKind() == kind::APPLY_UF)
      {
        Trace("e-solver")
            << t.getOperator()
            << " is a function,, using SyGuS for axiom instantiation"
            << std::endl;
        useSygus = true;
        break;
      }

      Node val = smt->getValue(t);
      if (val.isNull())
      {
        break;
      }
      tvs.emplace_back(val);
    }

    if (useSygus)
    {
      std::unique_ptr<SmtEngine> sygusChecker(new SmtEngine(nm));
      sygusChecker->getOptions().set(options::inputLanguage,
                                     language::input::LANG_SYGUS_V2);
      sygusChecker->getOptions().set(options::incrementalSolving, false);
      // sygusChecker->getOptions().set(options::sygusAbortSize, 2);
      // sygusChecker->getOptions().set(options::sygusRepairConst, true);
      sygusChecker->getOptions().set(options::sygusActiveGenMode,
                                     options::SygusActiveGenMode::ENUM);
      sygusChecker->setIsInternalSubsolver();
      sygusChecker->setTimeLimit(instantiator->d_timeout);

      Node f = abstractAsserts.size() == 0
                   ? nm->mkConst(true)
                   : (abstractAsserts.size() == 1
                          ? abstractAsserts[0]
                          : nm->mkNode(kind::AND, abstractAsserts));

      std::vector<Node> funs;
      for (const Node& t : ts)
      {
        std::stringstream ss;
        ss << "f" << t.getOperator() << "_";
        Node fun = nm->mkBoundVar(ss.str(), t.getOperator().getType());
        funs.emplace_back(fun);
        Trace("e-solver") << "Synthesizing function " << fun << " with type "
                          << fun.getType() << std::endl;

        std::vector<Node> vars;
        Assert(t.getKind() == kind::APPLY_UF);
        for (const Node& v : t)
        {
          Node bv = nm->mkBoundVar("v", v.getType());
          vars.emplace_back(bv);
        }
        sygusChecker->declareSynthFun(fun, false, vars);

        f = f.substitute(TNode(t.getOperator()), TNode(fun));
        f = f.substitute(t.begin(), t.end(), vars.begin(), vars.end());
      }

      std::unordered_set<Node, NodeHashFunction> symss;
      expr::getSymbols(f, symss);

      std::vector<Node> fsyms;
      std::vector<Node> fsymModels;
      std::vector<Node> syms;
      for (const Node& n : symss)
      {
        if (std::find(ts.begin(), ts.end(), n) != ts.end())
        {
          continue;
        }

        if (n.getType().isFunction())
        {
          fsyms.emplace_back(n);
          fsymModels.emplace_back(smt->getValue(n));
        }
        else if (n.getType().getKind() != kind::SELECTOR_TYPE)
        {
          syms.emplace_back(n);
        }
      }

      f = f.substitute(
          fsyms.begin(), fsyms.end(), fsymModels.begin(), fsymModels.end());

      std::vector<Node> svars;
      for (const Node& sym : syms)
      {
        std::stringstream ss;
        ss << "s" << sym << "_";
        Node bv = nm->mkBoundVar(ss.str(), sym.getType());
        svars.emplace_back(bv);
        sygusChecker->declareSygusVar(bv);
        Trace("e-solver") << "SyGuS variable " << sym << " -> " << bv << " ("
                          << sym.getType() << ")" << std::endl;
      }
      f = f.substitute(syms.begin(), syms.end(), svars.begin(), svars.end());

      Trace("e-solver") << "f = " << f << std::endl;
      Trace("e-solver") << "syms = " << syms << std::endl;
      Trace("e-solver") << "Synthesizing... ";
      sygusChecker->assertSygusConstraint(f.notNode());
      Result sr = sygusChecker->checkSynth();
      Trace("e-solver") << sr << std::endl;

      if (sr.isSat() == Result::UNSAT)
      {
        std::map<Node, Node> fmap;
        sygusChecker->getSynthSolutions(fmap);

        Trace("e-solver") << "Found solution" << std::endl;
        Node qt = eBody;
        Assert(funs.size() == ts.size());
        for (size_t i = 0, size = funs.size(); i < size; i++)
        {
          Node t = ts[i];
          Node fun = funs[i];
          Node result = fmap[fun];
          Trace("e-solver") << "  " << fun << ": " << result << std::endl;
          qt = qt.substitute(TNode(t.getOperator()), TNode(result));
        }

        Node axiomInst = nm->mkNode(kind::IMPLIES, qt, eBody);
        Trace("e-solver") << "Adding axiom instance: " << axiomInst
                          << std::endl;
        toAssert.emplace_back(axiomInst);
      }
      else
      {
        Trace("e-solver") << "No solution found for synthesis problem"
                          << std::endl;
        instantiator->d_timeout *= 2;
      }
    }
    else
    {
      std::vector<Node> bvs;
      for (size_t i = 0, size = ts.size(); i < size; i++)
      {
        Node t = ts[i];
        std::stringstream ss;
        ss << "t" << i;
        bvs.emplace_back(nm->mkBoundVar(ss.str(), t.getType()));
      }
      Node bvl = nm->mkNode(kind::BOUND_VAR_LIST, bvs);
      Node qt = eBody.substitute(ts.begin(), ts.end(), bvs.begin(), bvs.end());
      Node qbody = nm->mkNode(kind::IMPLIES, qt, eBody);

      TypeNode boolType = nm->booleanType();
      Node qvar = nm->mkSkolem("qid", boolType);
      Node ip = nm->mkNode(kind::INST_ATTRIBUTE, qvar);
      Node ipl = nm->mkNode(kind::INST_PATTERN_LIST, ip);

      qvar.setAttribute(InternalQuantAttribute(), true);
      smt->setUserAttribute("qid", qvar, {}, "");

      Node axiom = nm->mkNode(kind::FORALL, bvl, qbody, ipl);
      axioms.emplace_back(axiom);
      Trace("e-solver") << "Adding axiom... " << axiom << std::endl;
    }

    smt->push();

    // Assert SAT assignment
    for (const Node& literal : literals)
    {
      smt->assertFormula(literal);
    }

    // Assert models of function symbols
    if (instantiator->d_assertFunctionModels)
    {
      for (const Node& asym : asyms)
      {
        if (asym.getType().isFunction())
        {
          Node val = fmodels[asym];
          std::vector<Node> args(val[0].begin(), val[0].end());
          Trace("e-solver") << "Asserting function model " << asym << " = "
                            << val << std::endl;
          smt->defineFunction(asym, args, val[1]);
        }
      }
    }

    Node qt;
    for (const Node& axiom : axioms)
    {
      Trace("e-solver") << "Testing axiom " << axiom << "... ";
      smt->push();
      smt->assertFormula(axiom);
      smt->setTimeLimit(instantiator->d_timeout);
      Result ar = smt->checkSat();
      Trace("e-solver") << ar << std::endl;

      if (ar.isUnknown() && ar.whyUnknown() == Result::TIMEOUT)
      {
        timedOut = true;
      }

      if (ar.isSat() != Result::SAT)
      {
        std::vector<Node> qs;
        smt->getInstantiatedQuantifiedFormulas(qs);

        for (const Node& q : qs)
        {
          std::vector<std::vector<Node>> tvecs;
          smt->getInstantiationTermVectors(q, tvecs);
          Trace("e-solver") << "Quantifier: " << q << std::endl;
          for (const std::vector<Node>& tvec : tvecs)
          {
            bool skip = false;
            for (size_t i = 0, size = tvec.size(); i < size; i++)
            {
              Node tv = tvec[i];
              Node t = axiom[0][i];
              if (tv.getKind() == kind::WITNESS || t.getType() != tv.getType())
              {
                skip = true;
                break;
              }
            }
            if (skip)
            {
              continue;
            }

            Trace("e-solver") << "  Instantiations: " << tvec << std::endl;
            Node axiomInst = axiom[1].substitute(
                axiom[0].begin(), axiom[0].end(), tvec.begin(), tvec.end());
            toAssert.emplace_back(axiomInst);
            Node lemma = additionalLemmas(axiomInst);
            if (!lemma.isConst())
            {
              toAssert.emplace_back(lemma);
            }
          }
        }
      }
      smt->pop();
    }

    smt->pop();
    smt->pop();
  }

  JobOutput jo(worker, instantiator, toAssert, false);
  toAssert.clear();

  if (timedOut)
  {
    Trace("e-solver") << "Instantiator timed out, reinitializing" << std::endl;
    instantiator->d_assertFunctionModels =
        !instantiator->d_assertFunctionModels;
    worker->reinit();
    instantiator->d_timeout *= 2;
  }

  return std::make_pair(false, jo);
}

Result ESolver::isUnsat(Node f)
{
  NodeManager* nm = NodeManager::currentNM();
  SmtEngine* smtCurr = smt::currentSmtEngine();

  std::unordered_map<Node, Node, NodeHashFunction> cache;
  std::map<std::vector<Node>, std::pair<Node, Node>> eMap;
  std::unordered_map<TypeNode, std::vector<Node>, TypeNodeHashFunction>
      termIndex;
  std::unordered_set<Node, NodeHashFunction> axiomsSent;

  std::mutex abstractAssertsMut;
  Trace("e-solver") << "Original formula" << std::endl;
  std::vector<Node> abstractAsserts;
  Trace("e-solver") << "  " << f << std::endl;
  abstractAsserts.emplace_back(abstract(f, cache, eMap));
  Trace("e-solver") << std::endl;

  if (Trace.isOn("e-solver"))
  {
    Trace("e-solver") << "Mappings" << std::endl;
    for (const std::pair<const std::vector<Node>, std::pair<Node, Node>>&
             mapping : eMap)
    {
      Trace("e-solver") << "  " << mapping.first << " -> " << mapping.second
                        << std::endl;
    }
    Trace("e-solver") << std::endl;
  }

  std::unique_ptr<SmtEngine> mainChecker;
  theory::initializeSubsolver(mainChecker);
  mainChecker->getOptions().set(options::produceModels, true);
  mainChecker->getOptions().set(options::incrementalSolving, true);
  mainChecker->getOptions().set(options::eSolver, false);

  std::vector<std::unique_ptr<Instantiator>> instantiators;
  for (size_t i = 0; i < eMap.size(); i++)
  {
    Trace("e-solver") << "Creating instantiator (" << i << ")..." << std::endl;
    instantiators.emplace_back(new Instantiator(nm, smtCurr->getLogicInfo()));
  }

  {
    SmtScope smts(mainChecker.get());

    Trace("e-solver") << "Abstract formulas" << std::endl;
    for (const Node& a : abstractAsserts)
    {
      Trace("e-solver") << "  " << a << std::endl;
      mainChecker->assertFormula(a);
    }
  }

  size_t numThreads = eMap.size();
  if (options::numThreads() >= 1)
  {
    numThreads =
        std::min(numThreads, static_cast<size_t>(options::numThreads()));
  }
  bool pinning = (eMap.size() == numThreads);
  Trace("e-solver") << "Actual number of worker threads used: " << numThreads
                    << std::endl;
  Trace("e-solver") << "Pinning: " << pinning << std::endl;

  std::vector<std::unique_ptr<Worker>> workerInfos;
  for (size_t i = 0; i < numThreads; i++)
  {
    workerInfos.emplace_back(new Worker(i, nm, smtCurr->getLogicInfo()));
  }

  SmtScope smts(mainChecker.get());

  for (std::unique_ptr<Worker>& worker : workerInfos)
  {
    for (const Node& a : abstractAsserts)
    {
      NodeManagerScope nms(worker->d_interNm);
      worker->d_abstractAssertsBuffer.emplace_back(
          worker->d_vmMainInter.importNode(a));
    }
  }

  size_t i = 0;
  std::vector<std::pair<Node, std::pair<Node, Node>>> tVars;
  for (const std::pair<const std::vector<Node>, std::pair<Node, Node>>&
           mapping : eMap)
  {
    Instantiator* instantiator = instantiators[i].get();
    Node eBody = mapping.second.second;

    std::unordered_set<Node, NodeHashFunction> fvs;
    expr::getFreeVariables(eBody, fvs);

    std::vector<Node> args;
    std::vector<TypeNode> argTypes;
    for (const Node& fv : fvs)
    {
      args.emplace_back(fv);
      argTypes.emplace_back(fv.getType());
    }

    std::vector<Node> qtVars;
    const std::vector<Node>& eVars = mapping.first;
    for (const Node& eVar : eVars)
    {
      Node t;
      if (args.size() > 0)
      {
        TypeNode fnt = nm->mkFunctionType(argTypes, eVar.getType());
        std::vector<Node> largs = {nm->mkSkolem("t", fnt)};
        largs.insert(largs.end(), args.begin(), args.end());
        t = nm->mkNode(kind::APPLY_UF, largs);
      }
      else
      {
        t = nm->mkSkolem("t", eVar.getType());
      }

      qtVars.emplace_back(t);
      tVars.emplace_back(std::make_pair(t, std::make_pair(eVar, eBody)));
    }

    // Each instantiator negates one e-constant
    Node cube = eBody;
    instantiator->d_cube = cube;
    Trace("e-solver") << "Set cube " << cube << std::endl;

    for (const Node& eVar : eVars)
    {
      instantiator->d_key.emplace_back(eVar);
    }
    instantiator->d_eBody = eBody;
    /*
    {
      NodeManagerScope nms(instantiator->getNodeManager());
      Node cube = instantiator->d_vm.importNode(eBody).notNode();
      Trace("e-solver") << "Asserting cube " << cube << std::endl;
      instantiator->d_smt->assertFormula(cube);

      // TODO: Ugly/unnecessary work
      for (const Node& eVar : eVars) {
        instantiator->d_key.emplace_back(instantiator->d_vm.importNode(eVar));
      }
    }
    */
    i++;
  }

  Trace("e-solver") << std::endl;

  ThreadPool<Worker, JobOutput> pool(workerInfos, numThreads, pinning);

  CodeTimer eSolverTimer(d_eSolverTime);

  for (std::unique_ptr<Worker>& worker : workerInfos)
  {
    worker->d_smt->setOutOfResourcesCallback(
        [&pool]() { return pool.stopped(); });
    worker->d_pool = &pool;
  }

  for (std::unique_ptr<Instantiator>& instantiator : instantiators)
  {
    Instantiator* instantiatorPtr = instantiator.get();
    pool.scheduleTask([instantiatorPtr](Worker* worker) {
      return refine(worker, instantiatorPtr);
    });
  }

  bool recheck = true;
  std::vector<Node> toAssert;
  while (true)
  {
    if (recheck)
    {
      Result r;
      Trace("e-solver") << "Check assertions... ";
      {
        CodeTimer mainSolverTimer(d_mainSolverTime);
        d_numMainChecks += 1;
        // mainChecker->setTimeLimit(timeout);
        r = mainChecker->checkSat();
      }
      Trace("e-solver") << r << std::endl;
      if (r.isSat() == Result::UNSAT)
      {
        pool.stop();
        for (std::unique_ptr<Worker>& worker : workerInfos)
        {
          Trace("e-solver") << "Notifying worker to shut down" << std::endl;
          worker->d_abstractAssertsBufferCv.notify_one();
        }
        return r;
      } /* else if (r.isUnknown()) {
        timeout *= 2;
        recheck = true;
      } */
      else
      {
        recheck = false;
      }
    }

    Trace("e-solver") << "Waiting for next result" << std::endl;
    std::vector<std::pair<size_t, JobOutput>> resv;
    {
      CodeTimer mainSolverTimer(d_mainWaitTime);
      if (!pool.getResult(resv))
      {
        break;
      }
    }

    d_numRounds += 1;
    for (std::pair<size_t, JobOutput>& res : resv)
    {
      JobOutput& jo = res.second;

      if (jo.d_toAssert.empty())
      {
        Trace("e-solver") << "No axioms" << std::endl;
      }
      else
      {
        // Assert new axioms and share with instantiators
        for (const Node& a : jo.d_toAssert)
        {
          Node axiomInst = jo.d_worker->d_vmMainInter.exportNode(a);
          if (axiomsSent.find(axiomInst) != axiomsSent.end())
          {
            Trace("e-solver")
                << "Skipping axiom instance: " << axiomInst << std::endl;
          }
          else
          {
            Trace("e-solver")
                << "Asserting axiom instance: " << axiomInst << std::endl;
            recheck = true;
            d_numAxioms += jo.d_toAssert.size();
            mainChecker->assertFormula(axiomInst);
            abstractAsserts.emplace_back(axiomInst);
            axiomsSent.insert(axiomInst);

            for (std::unique_ptr<Worker>& worker : workerInfos)
            {
              std::unique_lock<std::mutex> lock(
                  worker->d_abstractAssertsBufferMut);
              NodeManagerScope nms(worker->d_interNm);
              worker->d_abstractAssertsBuffer.emplace_back(
                  worker->d_vmMainInter.importNode(axiomInst));
            }
          }
        }
      }

      jo.clear();

      {
        std::unique_lock<std::mutex> lock(
            jo.d_worker->d_abstractAssertsBufferMut);
        jo.d_worker->d_ready = true;
      }
      jo.d_worker->d_abstractAssertsBufferCv.notify_one();

      if (jo.d_done)
      {
        Trace("e-solver") << "Instantiator done, not rescheduling" << std::endl;
      }
      else
      {
        if (pinning)
        {
          pool.notifyNextTask(res.first);
        }
        else
        {
          // If we are not pinning, we have to reschedule
          Instantiator* instantiatorPtr = jo.d_instantiator;
          // Schedule instantiator again
          pool.scheduleTask([instantiatorPtr](Worker* worker) {
            return refine(worker, instantiatorPtr);
          });
        }
      }
    }

    Trace("e-solver") << std::endl;
  }

  Result r(Result::SAT_UNKNOWN, Result::INCOMPLETE);
  return r;
}

Node ESolver::abstract(Node n,
                       std::unordered_map<Node, Node, NodeHashFunction>& cache,
                       std::map<std::vector<Node>, std::pair<Node, Node>>& eMap)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> toVisit{n};
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (cache.find(curr) != cache.end())
    {
      Node result = cache[curr];
      if (result.isNull())
      {
        Node newNode;
        if (curr.getKind() == kind::FORALL || curr.getKind() == kind::EXISTS)
        {
          bool negate = curr.getKind() == kind::FORALL;
          Node bvl = curr[0];
          Node newBody = cache[curr[1]];

          std::unordered_set<Node, NodeHashFunction> fvs;
          expr::getFreeVariables(curr, fvs);

          std::vector<Node> args;
          std::vector<TypeNode> argTypes;
          for (const Node& fv : fvs)
          {
            args.emplace_back(fv);
            argTypes.emplace_back(fv.getType());
          }

          std::vector<Node> es;
          for (Node var : bvl)
          {
            Node e;
            if (args.size() > 0)
            {
              TypeNode fnt = nm->mkFunctionType(argTypes, var.getType());
              std::vector<Node> largs = {nm->mkSkolem("l", fnt)};
              largs.insert(largs.end(), args.begin(), args.end());
              e = nm->mkNode(kind::APPLY_UF, largs);
            }
            else
            {
              e = nm->mkSkolem("l", var.getType());
            }
            es.emplace_back(e);
            newBody = newBody.substitute(TNode(var), TNode(e));
            // TODO: Ugly and inefficient
            for (std::pair<const std::vector<Node>, std::pair<Node, Node>>&
                     mapping : eMap)
            {
              mapping.second = std::make_pair(
                  mapping.second.first,
                  mapping.second.second.substitute(TNode(var), TNode(e)));
            }
          }

          eMap[es] =
              std::make_pair(es[0], negate ? newBody.notNode() : newBody);
          cache[curr] = newBody;
        }
        else
        {
          NodeBuilder<> nb(curr.getKind());
          if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            nb << cache[curr.getOperator()];
          }
          for (const Node& currc : curr)
          {
            nb << cache[currc];
          }
          cache[curr] = nb;
        }
      }
      continue;
    }
    else if (curr.getNumChildren() == 0)
    {
      cache[curr] = curr;
      continue;
    }

    cache[curr] = Node::null();
    toVisit.emplace_back(curr);
    if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      toVisit.push_back(curr.getOperator());
    }
    toVisit.insert(toVisit.end(), curr.begin(), curr.end());
  }

  return cache[n];
}

Node mapConsts(Node n, std::unordered_map<Node, Node, NodeHashFunction>& cache)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> toVisit{n};
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (cache.find(curr) != cache.end())
    {
      Node result = cache[curr];
      if (!result.isNull())
      {
        continue;
      }

      if (curr.getKind() == kind::UNINTERPRETED_CONSTANT)
      {
        Node c = nm->mkSkolem("uc", curr.getType());
        cache[curr] = c;
      }
      else if (curr.getNumChildren() == 0)
      {
        cache[curr] = curr;
      }
      else
      {
        NodeBuilder<> nb(curr.getKind());
        if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          nb << cache[curr.getOperator()];
        }
        for (const Node& currc : curr)
        {
          nb << cache[currc];
        }
        cache[curr] = nb;
      }
      continue;
    }

    cache[curr] = Node::null();
    toVisit.emplace_back(curr);
    if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      toVisit.push_back(curr.getOperator());
    }
    toVisit.insert(toVisit.end(), curr.begin(), curr.end());
  }

  return cache[n];
}

void ESolver::apps(Node f, Node n, std::vector<Node>& result)
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

    if (curr.getKind() == kind::APPLY_UF && curr.getOperator() == f)
    {
      result.emplace_back(curr);
    }

    toVisit.emplace_back(curr);
    if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      toVisit.push_back(curr.getOperator());
    }
    toVisit.insert(toVisit.end(), curr.begin(), curr.end());
  }
}

bool ESolver::hasTVar(Node t, Node n)
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

    if (curr == t)
    {
      return true;
    }

    toVisit.emplace_back(curr);
    if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      toVisit.push_back(curr.getOperator());
    }
    toVisit.insert(toVisit.end(), curr.begin(), curr.end());
  }

  return false;
}

Node additionalLemmas(Node inst)
{
  NodeManager* nm = NodeManager::currentNM();
  VirtualTermSkolemAttribute vtsa;
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<Node> toVisit{inst};
  Node lemmas = nm->mkConst(true);
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (visited.find(curr) != visited.end())
    {
      continue;
    }
    visited.insert(curr);

    if (curr.getKind() == kind::SKOLEM)
    {
      if (curr.getAttribute(vtsa))
      {
        lemmas =
            nm->mkNode(kind::AND,
                       lemmas,
                       nm->mkNode(kind::GT, curr, nm->mkConst(Rational(0))));
      }
    }

    toVisit.emplace_back(curr);
    if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      toVisit.push_back(curr.getOperator());
    }
    toVisit.insert(toVisit.end(), curr.begin(), curr.end());
  }
  return lemmas;
}

Node collapseQuantifiers(Node f)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction> results;
  std::vector<Node> toVisit{f};
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    if (results.find(curr) != results.end())
    {
      Node result = results[curr];
      if (result.isNull())
      {
        Node newNode;
        if ((curr.getKind() == kind::FORALL || curr.getKind() == kind::EXISTS)
            && curr.getKind() == curr[1].getKind())
        {
          std::vector<Node> bvs;
          bvs.insert(bvs.end(), curr[0].begin(), curr[0].end());
          bvs.insert(bvs.end(), curr[1][0].begin(), curr[1][0].end());
          results[curr] = nm->mkNode(curr.getKind(),
                                     nm->mkNode(kind::BOUND_VAR_LIST, bvs),
                                     curr[1][1]);
        }
        else
        {
          NodeBuilder<> nb(curr.getKind());
          if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            nb << results[curr.getOperator()];
          }
          for (const Node& currc : curr)
          {
            nb << results[currc];
          }
          results[curr] = nb;
        }
      }
      continue;
    }
    else if (curr.getNumChildren() == 0)
    {
      results[curr] = curr;
      continue;
    }

    results[curr] = Node::null();
    toVisit.emplace_back(curr);
    if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      toVisit.push_back(curr.getOperator());
    }
    toVisit.insert(toVisit.end(), curr.begin(), curr.end());
  }

  return results[f];
}

}  // namespace smt
}  // namespace CVC4
