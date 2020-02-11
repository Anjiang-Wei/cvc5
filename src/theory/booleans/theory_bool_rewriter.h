/*********************                                                        */
/*! \file theory_bool_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H
#define CVC4__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H

#include "theory/rewriter.h"
#include "theory/theory_rewriter.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBoolRewriter : public TheoryRewriter
{
 public:
  void registerRewrites(Rewriter* rewriter) override;
  RewriteResponse preRewrite(TNode n) override;
  RewriteResponse postRewrite(TNode n) override;

 private:
  /**
   * Rewrites nodes of kind `NOT`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteNot(RewriteEnvironment* re, TNode n);

  /**
   * Rewrites nodes of kind `OR`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteOr(RewriteEnvironment* re, TNode n);

  /**
   * Rewrites nodes of kind `AND`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteAnd(RewriteEnvironment* re, TNode n);

  /**
   * Rewrites nodes of kind `IMPLIES`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteImplies(RewriteEnvironment* re, TNode n);

  /**
   * Rewrites nodes of kind `EQUAL`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteEqual(RewriteEnvironment* re, TNode n);

  /**
   * Rewrites nodes of kind `XOR`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteXor(RewriteEnvironment* re, TNode n);

  /**
   * Rewrites nodes of kind `ITE`.
   *
   * @param re The rewrite environment
   * @param n The node to rewrite
   * @return The result of rewriting `n`
   */
  static RewriteResponse rewriteIte(RewriteEnvironment* re, TNode n);
}; /* class TheoryBoolRewriter */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H */
