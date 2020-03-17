/*********************                                                        */
/*! \file theory_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The TheoryRewriter class
 **
 ** The TheoryRewriter class is the interface that theory rewriters implement.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_REWRITER_H
#define CVC4__THEORY__THEORY_REWRITER_H

#include "expr/node.h"
#include "theory/rewrite_response.h"
#include "theory/rewriter/rules.h"

namespace CVC4 {
namespace theory {

class Rewriter;

/**
 * The interface that a theory rewriter has to implement.
 *
 * Note: A theory rewriter is expected to handle all kinds of a theory, even
 * the ones that are removed by `Theory::expandDefinition()` since it may be
 * called on terms before the definitions have been expanded.
 */
class TheoryRewriter
{
 public:
  virtual ~TheoryRewriter() = default;

  /**
   * Registers the rewrites of a given theory with the rewriter.
   *
   * @param rewriter The rewriter to register the rewrites with.
   */
  virtual void registerRewrites(Rewriter* rewriter) {}

  /**
   * Performs a pre-rewrite step.
   *
   * @param node The node to rewrite
   */
  virtual RewriteResponse postRewrite(TNode node) = 0;

  /**
   * Performs a post-rewrite step.
   *
   * @param node The node to rewrite
   */
  virtual RewriteResponse preRewrite(TNode node) = 0;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__THEORY_REWRITER_H */
