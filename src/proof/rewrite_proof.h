/*********************                                                        */
/*! \file rewrite_proof.h
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

#include "cvc4_private.h"

#ifndef CVC4__PROOF__REWRITE_PROOF_H
#define CVC4__PROOF__REWRITE_PROOF_H

#include <vector>
#include <unordered_map>

#include "expr/node.h"
#include "proof/theory_proof.h"
#include "util/proof.h"
#include "theory/rewriter/rules.h"

namespace CVC4 {

struct RewriteStep {
  // The type of the rewrite
  theory::rules::RewriteRule d_tag = theory::rules::RewriteRule::UNKNOWN;
  // Node before the rewrite
  Node d_original;
  Node d_rewritten;
  // Rewrite proofs for children
  std::vector<RewriteStep *> d_children;
  // Subproofs
  std::vector<RewriteStep *> d_subproofs;
  // Unique id to identify the rewrite
  unsigned d_id;
  // Stores whether the cached version of this rewrite is ever used
  bool d_cached_version_used = false;
  // XXX: refactor into seperate class
  unsigned swap_id1, swap_id2;

  RewriteStep(const Node original)
      : d_original(original) {
    d_id = ProofLetCount::newId();
  }
  RewriteStep(theory::rules::RewriteRule tag, const Node original)
      : d_tag(tag), d_original(original) {
    d_id = ProofLetCount::newId();
  }
  ~RewriteStep();

  void deleteUncachedChildren();
  void print(int tab) const;
  bool isLeaf() const { return d_children.size() == 0; }
};

typedef std::unordered_map<Node, RewriteStep *, NodeHashFunction> ProofCache;
typedef std::unordered_map<Node, RewriteStep *, NodeHashFunction>::const_iterator
    ProofCacheIterator;

class RewriteProof {
private:
  std::vector<RewriteStep *> d_rewrites;
  ProofCache preRewriteCache;
  ProofCache postRewriteCache;

public:
  RewriteProof() {}
  ~RewriteProof();

  void addRewrite(RewriteStep *rewrite) { d_rewrites.push_back(rewrite); }

  void attachSubproofToParent();

  RewriteStep *getRewrite() const;
  RewriteStep *getTopRewrite() const { return d_rewrites.back(); };

  void registerRewrite(theory::rules::RewriteRule tag, Node rewritten);
  void registerSwap(const unsigned swap_id1, const unsigned swap_id2);
  void replaceRewrite(RewriteStep *rewrite);

  RewriteStep *getPreRewriteCache(Node node);
  RewriteStep *getPostRewriteCache(Node node);
  void setPreRewriteCache(Node node, RewriteStep *rewrite);
  void setPostRewriteCache(Node node, RewriteStep *rewrite);

  void printCachedProofs(TheoryProofEngine *tp, std::ostream &os,
                         std::ostream &paren, ProofLetMap &globalLetMap) const;
};

} /* CVC4 namespace */

#endif
