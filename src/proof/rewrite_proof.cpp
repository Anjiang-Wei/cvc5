/*********************                                                        */
/*! \file rewrite_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of a rewrite proof
 **/

#include "proof/rewrite_proof.h"

#include "proof_manager.h"
#include "theory/rewriter.h"
#include "theory/rewriter/rules_printer.h"

namespace CVC4 {

RewriteStep::~RewriteStep()
{
  for (size_t i = 0; i < d_subproofs.size(); i++)
  {
    delete d_subproofs[i];
  }
}

void RewriteStep::deleteUncachedChildren()
{
  for (size_t i = 0; i < d_children.size(); i++)
  {
    if (d_children[i] != NULL)
    {
      d_children[i]->deleteUncachedChildren();
      if (!d_children[i]->d_cached_version_used)
      {
        delete d_children[i];
        d_children[i] = NULL;
      }
    }
  }
}

void RewriteStep::print(int tab) const
{
  /*
  for (int j = 0; j < tab; j++)
    std::cout << " ";
  std::cout << d_tag << " > " << d_original << " < " << std::endl;

  for (size_t i = 0; i < d_children.size(); i++) {
    d_children[i]->print(tab + 1);
    std::cout << std::endl;
  }
  */
}

RewriteProof::~RewriteProof()
{
  for (ProofCacheIterator iter = preRewriteCache.begin();
       iter != preRewriteCache.end();
       ++iter)
  {
    if (!iter->second->d_cached_version_used)
    {
      preRewriteCache[iter->first] = NULL;
    }
  }
  /*
  for (ProofCacheIterator iter = postRewriteCache.begin();
       iter != postRewriteCache.end(); ++iter) {
    if (!iter->second->d_cached_version_used) {
      postRewriteCache[iter->first] = NULL;
    }
  }*/

  for (size_t i = 0; i < d_rewrites.size(); i++)
  {
    d_rewrites[i]->deleteUncachedChildren();
    if (!d_rewrites[i]->d_cached_version_used)
    {
      delete d_rewrites[i];
    }
  }

  for (ProofCacheIterator iter = preRewriteCache.begin();
       iter != preRewriteCache.end();
       ++iter)
  {
    if (iter->second != NULL)
    {
      delete iter->second;
    }
  }
  /*
  for (ProofCacheIterator iter = postRewriteCache.begin();
       iter != postRewriteCache.end(); ++iter) {
    if (iter->second != NULL) {
      delete iter->second;
    }
  }*/
}

void RewriteProof::attachSubproofToParent()
{
  RewriteStep* topRewrite = d_rewrites.back();

  // Simplify proof
  if (topRewrite->d_tag == theory::rules::RewriteRule::NONE)
  {
    bool allChildrenRefl = true;
    for (size_t i = 0; i < topRewrite->d_children.size(); i++)
    {
      if (topRewrite->d_children[i]->d_tag != theory::rules::RewriteRule::NONE)
      {
        allChildrenRefl = false;
        break;
      }
    }
    if (allChildrenRefl)
    {
      topRewrite->d_children.clear();
    }
  }
  d_rewrites[d_rewrites.size() - 2]->d_children.push_back(d_rewrites.back());
  d_rewrites.pop_back();
}

RewriteStep* RewriteProof::getRewrite() const
{
  Assert(d_rewrites.size() == 1);
  return d_rewrites[0];
}

void RewriteProof::registerRewrite(theory::rules::RewriteRule tag)
{
  RewriteStep* topRewrite = d_rewrites.back();
  d_rewrites.pop_back();
  RewriteStep* newRewrite = new RewriteStep(tag, topRewrite->d_original);
  newRewrite->d_children.push_back(topRewrite);
  d_rewrites.push_back(newRewrite);
}

void RewriteProof::registerSwap(const unsigned swap_id1,
                                const unsigned swap_id2)
{
  // Register swap if it does not swap head with head
  if (swap_id1 != swap_id2)
  {
    /*
    RewriteStep *topRewrite = d_rewrites.back();
    d_rewrites.pop_back();
    RewriteStep *newRewrite = new RewriteStep(SWAP, topRewrite->d_original);
    newRewrite->swap_id1 = swap_id1;
    newRewrite->swap_id2 = swap_id2;
    newRewrite->d_children.push_back(topRewrite);
    d_rewrites.push_back(newRewrite);
    */
  }
}

void RewriteProof::replaceRewrite(RewriteStep* rewrite)
{
  // XXX: make sure that this is always safe
  delete d_rewrites.back();
  d_rewrites.back() = rewrite;
}

RewriteStep* RewriteProof::getPreRewriteCache(Node node)
{
  return NULL;  // preRewriteCache[node];
}

RewriteStep* RewriteProof::getPostRewriteCache(Node node)
{
  return NULL;  // postRewriteCache[node];
}

void RewriteProof::setPreRewriteCache(Node node, RewriteStep* rewrite)
{
  preRewriteCache[node] = rewrite;
}

void RewriteProof::setPostRewriteCache(Node node, RewriteStep* rewrite)
{
  postRewriteCache[node] = rewrite;
}

void RewriteProof::printCachedProofs(TheoryProofEngine* tp,
                                     std::ostream& os,
                                     std::ostream& paren,
                                     ProofLetMap& globalLetMap) const
{
  for (ProofCacheIterator iter = preRewriteCache.begin();
       iter != preRewriteCache.end();
       ++iter)
  {
    if (iter->second->d_cached_version_used)
    {
      os << std::endl;
      os << "(@ let" << iter->second->d_id << " ";
      theory::rules::RewriteProofPrinter::printRewriteProof(
          false, tp, iter->second, os, globalLetMap);
      paren << ")";
    }
  }
}

}  // namespace CVC4
