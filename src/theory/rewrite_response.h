/*********************                                                        */
/*! \file rewrite_response.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of a rewrite response
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__REWRITE_RESPONSE_H
#define CVC4__THEORY__REWRITE_RESPONSE_H

#include "expr/node.h"
#include "theory/rewriter/rules.h"

namespace CVC4 {
namespace theory {

class Rewriter;

/**
 * Theory rewriters signal whether more rewriting is needed (or not)
 * by using a member of this enumeration.  See RewriteResponse, below.
 */
enum RewriteStatus
{
  /** The node is fully rewritten (no more rewrites apply) */
  REWRITE_DONE,
  /** The node may be rewritten further */
  REWRITE_AGAIN,
  /** Subnodes of the node may be rewritten further */
  REWRITE_AGAIN_FULL
}; /* enum RewriteStatus */

/**
 * Instances of this class serve as response codes from
 * TheoryRewriter::preRewrite() and TheoryRewriter::postRewrite(). The response
 * consists of the rewritten node as well as a status that indicates whether
 * more rewriting is needed or not.
 */
struct RewriteResponse
{
  const RewriteStatus d_status;
  const Node d_node;
  const rules::RewriteRule d_rule = rules::RewriteRule::UNKNOWN;

  RewriteResponse(RewriteStatus status, Node n) : d_status(status), d_node(n) {}
  RewriteResponse(RewriteStatus status, Node n, rules::RewriteRule rule) : d_status(status), d_node(n), d_rule(rule) {}
}; /* struct RewriteResponse */

}
}

#endif
