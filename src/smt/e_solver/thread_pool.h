/*********************                                                        */
/*! \file thread_pool.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An implementation of a thread pool
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__E_SOLVER__THREAD_POOL_H
#define CVC4__SMT__E_SOLVER__THREAD_POOL_H

#include <condition_variable>
#include <future>
#include <mutex>
#include <queue>
#include <thread>
#include <unordered_map>

#include "expr/attribute.h"
#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/smt_engine_state.h"
#include "util/result.h"

namespace CVC4 {
namespace smt {

template <class W, class R>
class ThreadPool
{
 public:
  ThreadPool(std::vector<std::unique_ptr<W>>& workerInfos,
             ssize_t threads,
             bool pinning)
      : d_workerInfos(workerInfos),
        d_stop(false),
        d_pinning(pinning),
        d_process(-1)
  {
    for (ssize_t i = 0; i < threads; ++i)
    {
      d_workers.emplace_back([this, i, &workerInfos] {
        std::function<std::pair<bool, R>(W*)> task;
        bool fetchTask = true;
        for (;;)
        {
          if (fetchTask)
          {
            std::unique_lock<std::mutex> lock(this->d_queueMutex);
            this->d_cv.wait(lock, [this] {
              return this->d_stop || !this->d_tasks.empty();
            });
            if (this->d_stop)
            {
              Trace("e-solver") << "Shutting down thread" << std::endl;
              break;
            }
            task = std::move(this->d_tasks.front());
            this->d_tasks.pop();

            if (this->d_pinning)
            {
              // If we are using pinning, we just execute the same task over and
              // over again
              fetchTask = false;
            }
          }
          else
          {
            std::unique_lock<std::mutex> lock(this->d_queueMutex);
            this->d_cv.wait(lock, [this, i] {
              return this->d_stop || this->d_process == i;
            });
            this->d_process = -1;
            if (this->d_stop)
            {
              break;
            }
          }

          std::pair<bool, R> res = task(workerInfos[i].get());
          if (this->d_pinning && res.first)
          {
            // Exit if this thread has no more work to do and pinning is
            // enabled
            break;
          }
          else
          {
            std::unique_lock<std::mutex> lock(this->d_resultsMut);
            d_results.emplace(std::make_pair(i, res.second));
            // Clear object while holding the lock to make sure that the
            // NodeManager is not used simultaneously to delete the result and
            // to copy the result to the main thread.
            res.second.clear();
          }
          d_cvResults.notify_one();
        }
      });
    }
  }

  ~ThreadPool()
  {
    Trace("e-solver") << "Shutting down thread pool" << std::endl;
    {
      std::unique_lock<std::mutex> lock(d_queueMutex);
      d_stop = true;
    }
    d_cv.notify_all();
    for (std::thread& worker : d_workers)
    {
      worker.join();
    }
    Trace("e-solver") << "Joined all threads" << std::endl;
  }

  void stop()
  {
    std::unique_lock<std::mutex> lock(d_queueMutex);
    d_stop = true;
  }

  bool stopped() { return d_stop; }

  void scheduleTask(std::function<std::pair<bool, R>(W*)>&& f)
  {
    {
      std::unique_lock<std::mutex> lock(d_queueMutex);
      if (d_stop) throw std::runtime_error("enqueue on stopped ThreadPool");
      d_tasks.emplace(f);
    }
    d_cv.notify_one();
  }

  void notifyNextTask(size_t hint)
  {
    {
      std::unique_lock<std::mutex> lock(d_queueMutex);
      d_process = hint;
    }
    d_cv.notify_all();
  }

  bool getResult(std::vector<std::pair<size_t, R>>& out)
  {
    {
      std::unique_lock<std::mutex> lock(this->d_resultsMut);
      this->d_cvResults.wait(
          lock, [this] { return this->d_stop || !this->d_results.empty(); });
      if (this->d_stop)
      {
        return false;
      }
      Trace("e-solver") << "Number of results " << d_results.size()
                        << std::endl;
      while (!d_results.empty())
      {
        out.emplace_back(d_results.front());
        d_results.pop();
      }
    }
    return true;
  }

 private:
  std::vector<std::thread> d_workers;
  std::vector<std::unique_ptr<W>>& d_workerInfos;
  std::queue<std::function<std::pair<bool, R>(W*)>> d_tasks;
  std::queue<std::pair<size_t, R>> d_results;

  std::mutex d_queueMutex;
  std::condition_variable d_cv;

  std::mutex d_resultsMut;
  std::condition_variable d_cvResults;

  bool d_stop;
  bool d_pinning;
  ssize_t d_process;
};

}  // namespace smt
}  // namespace CVC4

#endif
