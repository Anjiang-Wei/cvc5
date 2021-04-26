/*********************                                                        */
/*! \file theory_bv_rewrite_rules_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Liana Hadarean, Clark Barrett
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

#pragma once

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter/rules_implementation.h"

namespace CVC4 {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ConcatFlatten>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT);
}

template<> inline
Node RewriteRule<ConcatFlatten>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ConcatFlatten>(" << node << ")" << std::endl;
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  std::vector<Node> processing_stack;
  processing_stack.push_back(node);
  while (!processing_stack.empty()) {
    Node current = processing_stack.back();
    processing_stack.pop_back();
    if (current.getKind() == kind::BITVECTOR_CONCAT) {
      for (int i = current.getNumChildren() - 1; i >= 0; i--)
        processing_stack.push_back(current[i]);
    } else {
      result << current;
    }
  }
  Node resultNode = result;
  Debug("bv-rewrite") << "RewriteRule<ConcatFlatten>(" << resultNode << ")" << std::endl;
  return resultNode;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ConcatExtractMerge>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<ConcatExtractMerge>::apply(TNode node) {
  return rules::ConcatExtractMerge(node).d_node;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ConcatConstantMerge>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<ConcatConstantMerge>::apply(TNode node) {
  return rules::ConcatConstantMerge(node).d_node;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractWhole>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<ExtractWhole>::apply(TNode node) {
  return rules::ExtractWhole(node).d_node;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractConstant>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  return true;
}

template<> inline
Node RewriteRule<ExtractConstant>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractConstant>(" << node << ")" << std::endl;
  Node child = node[0];
  BitVector childValue = child.getConst<BitVector>();
  return utils::mkConst(childValue.extract(utils::getExtractHigh(node), utils::getExtractLow(node)));
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractConcat>::applies(TNode node) {
  //Debug("bv-rewrite") << "RewriteRule<ExtractConcat>(" << node << ")" << std::endl;
  if (node.getKind() != kind::BITVECTOR_EXTRACT) return false;
  if (node[0].getKind() != kind::BITVECTOR_CONCAT) return false;
  return true;
}

template<> inline
Node RewriteRule<ExtractConcat>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractConcat>(" << node << ")" << std::endl;
  int extract_high = utils::getExtractHigh(node);
  int extract_low = utils::getExtractLow(node);

  std::vector<Node> resultChildren;

  Node concat = node[0];
  for (int i = concat.getNumChildren() - 1; i >= 0 && extract_high >= 0; i--) {
    Node concatChild = concat[i];
    int concatChildSize = utils::getSize(concatChild);
    if (extract_low < concatChildSize) {
      int extract_start = extract_low < 0 ? 0 : extract_low;
      int extract_end = extract_high < concatChildSize ? extract_high : concatChildSize - 1;
      resultChildren.push_back(utils::mkExtract(concatChild, extract_end, extract_start));
    }
    extract_low -= concatChildSize;
    extract_high -= concatChildSize;
  }

  std::reverse(resultChildren.begin(), resultChildren.end());

  return utils::mkConcat(resultChildren);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ExtractExtract>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<ExtractExtract>::apply(TNode node) {
  return rules::ExtractExtract(node).d_node;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<FailEq>::applies(TNode node) {
  //Debug("bv-rewrite") << "RewriteRule<FailEq>(" << node << ")" << std::endl;
  if (node.getKind() != kind::EQUAL) return false;
  if (node[0].getKind() != kind::CONST_BITVECTOR) return false;
  if (node[1].getKind() != kind::CONST_BITVECTOR) return false;
  return node[0] != node[1];
}

template<> inline
Node RewriteRule<FailEq>::apply(TNode node) {
  return utils::mkFalse();
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<SimplifyEq>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<SimplifyEq>::apply(TNode node) {
  return rules::SimplifyEq(node).d_node;
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<ReflexivityEq>::applies(TNode node) {
  return (node.getKind() == kind::EQUAL && node[0] < node[1]);
}

template<> inline
Node RewriteRule<ReflexivityEq>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ReflexivityEq>(" << node << ")" << std::endl;
  Node res = node[1].eqNode(node[0]);
  return res;
}

}
}
}
