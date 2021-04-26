/*********************                                                        */
/*! \file theory_bv_rewrite_rules_operator_elimination.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Clark Barrett
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

#include "options/bv_options.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter/rules_implementation.h"

namespace CVC4 {
namespace theory {
namespace bv {

template <>
inline bool RewriteRule<UgtEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<UgtEliminate>::apply(TNode node)
{
  return rules::UgtEliminate(node).d_node;
}

template <>
inline bool RewriteRule<UgeEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<UgeEliminate>::apply(TNode node)
{
  return rules::UgeEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SgtEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SgtEliminate>::apply(TNode node)
{
  return rules::SgtEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SgeEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SgeEliminate>::apply(TNode node)
{
  return rules::SgeEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SltEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SltEliminate>::apply(TNode node)
{
  return rules::SltEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SleEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SleEliminate>::apply(TNode node)
{
  return rules::SleEliminate(node).d_node;
}

template <>
inline bool RewriteRule<UleEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<UleEliminate>::apply(TNode node)
{
  return rules::UleEliminate(node).d_node;
}

template <>
inline bool RewriteRule<CompEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<CompEliminate>::apply(TNode node)
{
  return rules::CompEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SubEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SubEliminate>::apply(TNode node)
{
  return rules::SubEliminate(node).d_node;
}

template <>
inline bool RewriteRule<RepeatEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_REPEAT);
}

template <>
inline Node RewriteRule<RepeatEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<RepeatEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorRepeat>().d_repeatAmount;
  Assert(amount >= 1);
  if(amount == 1) {
    return a; 
  }
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  for(unsigned i = 0; i < amount; ++i) {
    result << node[0]; 
  }
  Node resultNode = result; 
  return resultNode;
}

template <>
inline bool RewriteRule<RotateLeftEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<RotateLeftEliminate>::apply(TNode node)
{
  return rules::RotateLeftEliminate(node).d_node;
}

template <>
inline bool RewriteRule<RotateRightEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<RotateRightEliminate>::apply(TNode node)
{
  return rules::RotateRightEliminate(node).d_node;
}

template <>
inline bool RewriteRule<BVToNatEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_TO_NAT);
}

template <>
inline Node RewriteRule<BVToNatEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<BVToNatEliminate>(" << node << ")" << std::endl;

  //if( node[0].isConst() ){
    //TODO? direct computation instead of term construction+rewriting
  //}
  return utils::eliminateBv2Nat(node);
}

template <>
inline bool RewriteRule<IntToBVEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::INT_TO_BITVECTOR);
}

template <>
inline Node RewriteRule<IntToBVEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<IntToBVEliminate>(" << node << ")" << std::endl;

  //if( node[0].isConst() ){
    //TODO? direct computation instead of term construction+rewriting
  //}
  return utils::eliminateInt2Bv(node);
}

template <>
inline bool RewriteRule<NandEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<NandEliminate>::apply(TNode node)
{
  return rules::NandEliminate(node).d_node;
}

template <>
inline bool RewriteRule<NorEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<NorEliminate>::apply(TNode node)
{
  return rules::NorEliminate(node).d_node;
}

template <>
inline bool RewriteRule<XnorEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<XnorEliminate>::apply(TNode node)
{
  return rules::XnorEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SdivEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SdivEliminate>::apply(TNode node)
{
  return rules::SdivEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SremEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SremEliminate>::apply(TNode node)
{
  return rules::SremEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SmodEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SmodEliminate>::apply(TNode node)
{
  return rules::SmodEliminate(node).d_node;
}

template <>
inline bool RewriteRule<ZeroExtendEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<ZeroExtendEliminate>::apply(TNode node)
{
  return rules::ZeroExtendEliminate(node).d_node;
}

template <>
inline bool RewriteRule<SignExtendEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<SignExtendEliminate>::apply(TNode node)
{
  return rules::SignExtendEliminate(node).d_node;
}

template <>
inline bool RewriteRule<RedorEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<RedorEliminate>::apply(TNode node)
{
  return rules::RedorEliminate(node).d_node;
}

template <>
inline bool RewriteRule<RedandEliminate>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<RedandEliminate>::apply(TNode node)
{
  return rules::RedandEliminate(node).d_node;
}

}
}
}
