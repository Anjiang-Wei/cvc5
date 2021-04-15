/*********************                                                        */
/*! \file worker.cpp
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

#include "smt/e_solver/worker.h"

namespace CVC4 {
namespace smt {

JobOutput::JobOutput()
    : d_worker(nullptr), d_instantiator(nullptr), d_toAssert({}), d_done(true)
{
}

JobOutput::JobOutput(Worker* worker,
                     Instantiator* instantiator,
                     const std::vector<Node>& toAssert,
                     bool done)
    : d_worker(worker), d_instantiator(instantiator), d_done(done)
{
  std::unique_lock<std::mutex> lock(d_worker->d_abstractAssertsBufferMut);
  d_worker->d_ready = false;

  NodeManagerScope nms(d_worker->d_interNm);
  for (const Node& n : toAssert)
  {
    d_toAssert.emplace_back(d_worker->d_vmInterWorker.exportNode(n));
  }
}

JobOutput::JobOutput(const JobOutput& other)
    : d_worker(other.d_worker), d_instantiator(other.d_instantiator)
{
  NodeManagerScope nms(d_worker->d_interNm);
  d_toAssert = other.d_toAssert;
  d_done = other.d_done;
}

JobOutput& JobOutput::operator=(const JobOutput& other)
{
  d_worker = other.d_worker;
  d_instantiator = other.d_instantiator;
  NodeManagerScope nms(d_worker->d_interNm);
  d_toAssert = other.d_toAssert;
  d_done = other.d_done;
  return *this;
}

void JobOutput::clear()
{
  NodeManagerScope nms(d_worker->d_interNm);
  d_toAssert.clear();
}

JobOutput::~JobOutput() { clear(); }

}  // namespace smt
}  // namespace CVC4
