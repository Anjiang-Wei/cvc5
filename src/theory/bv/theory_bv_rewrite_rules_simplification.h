/*********************                                                        */
/*! \file theory_bv_rewrite_rules_simplification.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Mathias Preiner
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
#include "theory/rewriter.h"
#include "theory/rewriter/rules_implementation.h"

namespace CVC4 {
namespace theory {
namespace bv {


/* -------------------------------------------------------------------------- */

/**
 * BvIteConstCond
 *
 * BITVECTOR_ITE with constant condition
 */
template <>
inline bool RewriteRule<BvIteConstCond>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteConstCond>::apply(TNode node)
{
  return rules::BvIteConstCond(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteEqualChildren
 *
 * BITVECTOR_ITE with term_then = term_else
 */
template <>
inline bool RewriteRule<BvIteEqualChildren>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteEqualChildren>::apply(TNode node)
{
  return rules::BvIteEqualChildren(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteConstChildren
 *
 * BITVECTOR_ITE with constant children of size one
 */
template <>
inline bool RewriteRule<BvIteConstChildren>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteConstChildren>::apply(TNode node)
{
  return rules::BvIteConstChildren(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteEqualCond
 *
 * Nested BITVECTOR_ITE with cond_outer == cond_inner
 *
 * c0 ? (c0 ? t0 : e0) : e1              ->  c0 ? t0 : e1
 * c0 ? t0             : (c0 ? t1 : e1)  ->  c0 ? t0 : e1
 * c0 ? (c0 ? t0 : e0) : (c0 ? t1 : e1)  ->  c0 ? t0 : e1
 */
template <>
inline bool RewriteRule<BvIteEqualCond>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteEqualCond>::apply(TNode node)
{
  Node n1 = rules::BvIteEqualCondThen(node).d_node;
  return rules::BvIteEqualCondElse(n1).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeThenIf
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? (c1 ? t1 : e1) : t1  ->  c0 AND NOT(c1) ? e1 : t1
 */
template <>
inline bool RewriteRule<BvIteMergeThenIf>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteMergeThenIf>::apply(TNode node)
{
  return rules::BvIteMergeThenIf(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeElseIf
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? (c1 ? t1 : e1) : e1  ->  c0 AND c1 ? t1 : e1
 */
template <>
inline bool RewriteRule<BvIteMergeElseIf>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteMergeElseIf>::apply(TNode node)
{
  return rules::BvIteMergeElseIf(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeThenElse
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? t0 : (c1 ? t0 : e1)  ->  NOT(c0) AND NOT(c1) ? e1 : t0
 */
template <>
inline bool RewriteRule<BvIteMergeThenElse>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteMergeThenElse>::apply(TNode node)
{
  return rules::BvIteMergeThenElse(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeElseElse
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? t0 : (c1 ? t1 : t0)  ->  NOT(c0) AND c1 ? t1 : t0
 */
template <>
inline bool RewriteRule<BvIteMergeElseElse>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvIteMergeElseElse>::apply(TNode node)
{
  return rules::BvIteMergeElseElse(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BvComp
 *
 * BITVECTOR_COMP of children of size 1 with one constant child
 */
template <>
inline bool RewriteRule<BvComp>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<BvComp>::apply(TNode node)
{
  return rules::BvComp(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * ShlByConst
 *
 * Left Shift by constant amount 
 */
template<> inline
bool RewriteRule<ShlByConst>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<ShlByConst>::apply(TNode node) {
  return rules::ShlByConst(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * LshrByConst
 *
 * Right Logical Shift by constant amount 
 */

template<> inline
bool RewriteRule<LshrByConst>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<LshrByConst>::apply(TNode node) {
  return rules::LshrByConst(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * AshrByConst
 *
 * Right Arithmetic Shift by constant amount 
 */

template<> inline
bool RewriteRule<AshrByConst>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<AshrByConst>::apply(TNode node) {
  return rules::AshrByConst(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BitwiseIdemp
 *
 * (a bvand a) ==> a
 * (a bvor a)  ==> a
 */

template<> inline
bool RewriteRule<BitwiseIdemp>::applies(TNode node) {
  Unreachable();
  return ((node.getKind() == kind::BITVECTOR_AND ||
           node.getKind() == kind::BITVECTOR_OR) &&
          node.getNumChildren() == 2 &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<BitwiseIdemp>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<BitwiseIdemp>(" << node << ")" << std::endl;
  return node[0]; 
}

/* -------------------------------------------------------------------------- */

/**
 * AndZero
 * 
 * (a bvand 0) ==> 0
 */

template<> inline
bool RewriteRule<AndZero>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_AND  &&
          node.getNumChildren() == 2 &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<> inline
Node RewriteRule<AndZero>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<AndZero>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/* -------------------------------------------------------------------------- */

/**
 * AndOne
 * 
 * (a bvand 1) ==> a
 */

template<> inline
bool RewriteRule<AndOne>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node);
  Node ones = utils::mkOnes(size); 
  return (node.getKind() == kind::BITVECTOR_AND  &&
          node.getNumChildren() == 2 &&
          (node[0] == ones ||
           node[1] == ones));
}

template<> inline
Node RewriteRule<AndOne>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<AndOne>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node);
  
  if (node[0] == utils::mkOnes(size)) {
    return node[1]; 
  } else {
    Assert(node[1] == utils::mkOnes(size));
    return node[0]; 
  }
}

/* -------------------------------------------------------------------------- */

/**
 * AndOrXorConcatPullUp
 *
 * Match:       x_m <op> concat(y_my, <const>_n, z_mz)
 *              <const>_n in { 0_n, 1_n, ~0_n }
 *
 * Rewrites to: concat(x[m-1:m-my]  <op> y,
 *                     x[m-my-1:mz] <op> <const>_n,
 *                     x[mz-1:0]    <op> z)
 */

template <>
inline bool RewriteRule<AndOrXorConcatPullUp>::applies(TNode node)
{
  return true;
  /*
  if (node.getKind() != kind::BITVECTOR_AND
      && node.getKind() != kind::BITVECTOR_OR
      && node.getKind() != kind::BITVECTOR_XOR)
  {
    return false;
  }

  TNode n;

  for (const TNode& c : node)
  {
    if (c.getKind() == kind::BITVECTOR_CONCAT)
    {
      for (const TNode& cc : c)
      {
        if (cc.isConst())
        {
          n = cc;
          break;
        }
      }
      break;
    }
  }
  if (n.isNull()) return false;
  return utils::isZero(n) || utils::isOne(n) || utils::isOnes(n);
  */
}

template <>
inline Node RewriteRule<AndOrXorConcatPullUp>::apply(TNode node)
{
  Node n1 = rules::AndPullUp(node).d_node;
  Node n2 = rules::OrPullUp(n1).d_node;
  return rules::XorPullUp(n2).d_node;
  /*
  Debug("bv-rewrite") << "RewriteRule<AndOrXorConcatPullUp>(" << node << ")"
                      << std::endl;
  uint32_t m, my, mz;
  size_t nc;
  Kind kind = node.getKind();
  TNode concat;
  Node x, y, z, c;
  NodeBuilder<> xb(kind);
  NodeBuilder<> yb(kind::BITVECTOR_CONCAT);
  NodeBuilder<> zb(kind::BITVECTOR_CONCAT);
  NodeBuilder<> res(kind::BITVECTOR_CONCAT);
  NodeManager* nm = NodeManager::currentNM();

  for (const TNode& child : node)
  {
    if (concat.isNull() && child.getKind() == kind::BITVECTOR_CONCAT)
    {
      concat = child;
    }
    else
    {
      xb << child;
    }
  }
  x = xb.getNumChildren() > 1 ? xb.constructNode() : xb[0];

  for (const TNode& child : concat)
  {
    if (c.isNull())
    {
      if (utils::isZero(child) || utils::isOne(child) || utils::isOnes(child))
      {
        c = child;
      }
      else
      {
        yb << child;
      }
    }
    else
    {
      zb << child;
    }
  }
  Assert(!c.isNull());
  Assert(yb.getNumChildren() || zb.getNumChildren());

  if ((nc = yb.getNumChildren()) > 0)
  {
    y = nc > 1 ? yb.constructNode() : yb[0];
  }
  if ((nc = zb.getNumChildren()) > 0)
  {
    z = nc > 1 ? zb.constructNode() : zb[0];
  }
  m = utils::getSize(x);
#ifdef CVC4_ASSERTIONS
  uint32_t n = utils::getSize(c);
#endif
  my = y.isNull() ? 0 : utils::getSize(y);
  mz = z.isNull() ? 0 : utils::getSize(z);
  Assert(mz == m - my - n);
  Assert(my || mz);

  if (my)
  {
    res << nm->mkNode(kind, utils::mkExtract(x, m - 1, m - my), y);
  }

  res << nm->mkNode(kind, utils::mkExtract(x, m - my - 1, mz), c);

  if (mz)
  {
    res << nm->mkNode(kind, utils::mkExtract(x, mz - 1, 0), z);
  }

  return res;
  */
}

/* -------------------------------------------------------------------------- */

/**
 * OrZero
 *
 * (a bvor 0) ==> a
 */

template<> inline
bool RewriteRule<OrZero>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_OR  &&
          node.getNumChildren() == 2 &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<> inline
Node RewriteRule<OrZero>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<OrZero>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node); 
  if (node[0] == utils::mkConst(size, 0)) {
    return node[1]; 
  } else {
    Assert(node[1] == utils::mkConst(size, 0));
    return node[0]; 
  }
}

/* -------------------------------------------------------------------------- */

/**
 * OrOne
 * 
 * (a bvor 1) ==> 1
 */

template<> inline
bool RewriteRule<OrOne>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node);
  Node ones = utils::mkOnes(size); 
  return (node.getKind() == kind::BITVECTOR_OR  &&
          node.getNumChildren() == 2 &&
          (node[0] == ones ||
           node[1] == ones));
}

template<> inline
Node RewriteRule<OrOne>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<OrOne>(" << node << ")" << std::endl;
  return utils::mkOnes(utils::getSize(node)); 
}

/* -------------------------------------------------------------------------- */

/**
 * XorDuplicate
 *
 * (a bvxor a) ==> 0
 */

template<> inline
bool RewriteRule<XorDuplicate>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node.getNumChildren() == 2 &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<XorDuplicate>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<XorDuplicate>(" << node << ")" << std::endl;
  return utils::mkZero(utils::getSize(node));
}

/* -------------------------------------------------------------------------- */

/**
 * XorOne
 *
 * (a bvxor 1) ==> ~a
 */

template<> inline
bool RewriteRule<XorOne>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<XorOne>::apply(TNode node)
{
  return rules::XorZero(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * XorZero
 *
 * (a bvxor 0) ==> a
 */

template<> inline
bool RewriteRule<XorZero>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<XorZero>::apply(TNode node)
{
  return rules::XorZero(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BitwiseNotAnd
 *
 * (a bvand (~ a)) ==> 0
 */

template<> inline
bool RewriteRule<BitwiseNotAnd>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_AND &&
          node.getNumChildren() == 2 &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<> inline
Node RewriteRule<BitwiseNotAnd>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<BitwiseNegAnd>(" << node << ")" << std::endl;
  return utils::mkZero(utils::getSize(node));
}

/* -------------------------------------------------------------------------- */

/**
 * BitwiseNegOr
 *
 * (a bvor (~ a)) ==> 1
 */

template<> inline
bool RewriteRule<BitwiseNotOr>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_OR &&
          node.getNumChildren() == 2 &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<> inline
Node RewriteRule<BitwiseNotOr>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<BitwiseNotOr>(" << node << ")" << std::endl;
  uint32_t size = utils::getSize(node);
  return utils::mkOnes(size);
}

/* -------------------------------------------------------------------------- */

/**
 * XorNot
 *
 * ((~ a) bvxor (~ b)) ==> (a bvxor b)
 */

template<> inline
bool RewriteRule<XorNot>::applies(TNode node) {
  Unreachable();
}

template <>
inline Node RewriteRule<XorNot>::apply(TNode node)
{
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<XorNot>(" << node << ")" << std::endl;
  Node a = node[0][0];
  Node b = node[1][0];
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_XOR, a, b);
}

/* -------------------------------------------------------------------------- */

/**
 * NotXor
 *
 * ~(a bvxor b) ==> (~ a bvxor b)
 */

template<> inline
bool RewriteRule<NotXor>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<NotXor>::apply(TNode node)
{
  return rules::NotXor(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * NotIdemp
 *
 * ~ (~ a) ==> a
 */

template<> inline
bool RewriteRule<NotIdemp>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<NotIdemp>::apply(TNode node) {
  return rules::NotIdemp(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * LtSelf
 *
 * a < a ==> false
 */

template<> inline
bool RewriteRule<LtSelf>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<LtSelf>::apply(TNode node) {
  Node n1 = rules::LtSelfUlt(node).d_node;
  return rules::LtSelfSlt(n1).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * LteSelf
 *
 * a <= a ==> true
 */

template<> inline
bool RewriteRule<LteSelf>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<LteSelf>::apply(TNode node) {
  Node n1 = rules::LteSelfUle(node).d_node;
  return rules::LteSelfSle(n1).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroUlt
 *
 * 0 < a ==> a != 0
 */

template <>
inline bool RewriteRule<ZeroUlt>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<ZeroUlt>::apply(TNode node)
{
  return rules::ZeroUlt(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UltZero
 *
 * a < 0 ==> false
 */

template<> inline
bool RewriteRule<UltZero>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<UltZero>::apply(TNode node) {
  return rules::UltZero(node).d_node;
}


/* -------------------------------------------------------------------------- */

/**
 * 
 */
template<> inline
bool RewriteRule<UltOne>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<UltOne>::apply(TNode node)
{
  return rules::UltOne(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * 
 */
template<> inline
bool RewriteRule<SltZero>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<SltZero>::apply(TNode node)
{
  return rules::SltZero(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UltSelf
 *
 * a < a ==> false
 */

template<> inline
bool RewriteRule<UltSelf>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<UltSelf>::apply(TNode node) {
  return rules::UltSelf(node).d_node;
}


/* -------------------------------------------------------------------------- */

/**
 * UleZero
 *
 * a <= 0 ==> a = 0
 */

template<> inline
bool RewriteRule<UleZero>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<UleZero>::apply(TNode node)
{
  return rules::UleZero(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UleSelf
 *
 * a <= a ==> true
 */

template<> inline
bool RewriteRule<UleSelf>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<UleSelf>::apply(TNode node) {
  return rules::UleSelf(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroUle
 *
 * 0 <= a ==> true
 */

template<> inline
bool RewriteRule<ZeroUle>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<ZeroUle>::apply(TNode node) {
  return rules::ZeroUle(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UleMax
 *
 * a <= 11..1 ==> true
 */

template<> inline
bool RewriteRule<UleMax>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<UleMax>::apply(TNode node) {
  return rules::UleMax(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * NotUlt
 *
 * ~ ( a < b) ==> b <= a
 */

template<> inline
bool RewriteRule<NotUlt>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<NotUlt>::apply(TNode node)
{
  return rules::NotUlt(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * NotUle
 *
 * ~ ( a <= b) ==> b < a
 */

template<> inline
bool RewriteRule<NotUle>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<NotUle>::apply(TNode node)
{
  return rules::NotUle(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * MultPow2
 *
 * (a * 2^k) ==> a[n-k-1:0] 0_k
 */

template <>
inline bool RewriteRule<MultPow2>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<MultPow2>::apply(TNode node)
{
  Node n1 = rules::MultPowX(node).d_node;
  return rules::MultPowXNeg(n1).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * ExtractMultLeadingBit
 *
 * If the bit-vectors multiplied have enough leading zeros,
 * we can determine that the top bits of the multiplication
 * are zero and not compute them. Only apply for large bitwidths
 * as this can interfere with other mult normalization rewrites such
 * as flattening. 
 */

template<> inline
bool RewriteRule<ExtractMultLeadingBit>::applies(TNode node) {
  return true; /*
  if (node.getKind() != kind::BITVECTOR_EXTRACT)
    return false;
  unsigned low = utils::getExtractLow(node);
  node = node[0];

  if (node.getKind() != kind::BITVECTOR_MULT ||
      node.getNumChildren() != 2 ||
      utils::getSize(node) <= 64)
    return false;

  if (node[0].getKind() != kind::BITVECTOR_CONCAT ||
      node[1].getKind() != kind::BITVECTOR_CONCAT ||
      !node[0][0].isConst() ||
      !node[1][0].isConst())
    return false;

  unsigned n = utils::getSize(node);
  // count number of leading zeroes
  const Integer& int1 = node[0][0].getConst<BitVector>().toInteger();
  const Integer& int2 = node[1][0].getConst<BitVector>().toInteger();
  size_t int1_size = utils::getSize(node[0][0]);
  size_t int2_size = utils::getSize(node[1][0]);
  unsigned zeroes1 = int1.isZero() ? int1_size : int1_size - int1.length();
  unsigned zeroes2 = int2.isZero() ? int2_size : int2_size - int2.length();

  // first k bits are not zero in the result
  unsigned k = 2 * n - (zeroes1 + zeroes2);

  if (k > low)
    return false; 

  return true; 
  */
}

template<> inline
Node RewriteRule<ExtractMultLeadingBit>::apply(TNode node) {
  return rules::ExtractMultLeadingBit(node).d_node;
  /*
  Debug("bv-rewrite") << "RewriteRule<MultLeadingBit>(" << node << ")" << std::endl;

  unsigned bitwidth = utils::getSize(node); 
  
  // node = node[0];
  // const Integer& int1 = node[0][0].getConst<BitVector>().toInteger();
  // const Integer& int2 = node[1][0].getConst<BitVector>().toInteger();
  // unsigned zeroes1 = int1.isZero()? utils::getSize(node[0][0]) :
  //                                   int1.length();

  // unsigned zeroes2 = int2.isZero()? utils::getSize(node[1][0]) :
  //                                   int2.length();
  // all bits >= k in the multiplier will have to be 0
  // unsigned n = utils::getSize(node); 
  // unsigned k = 2 * n - (zeroes1 + zeroes2);
  // Node extract1 = utils::mkExtract(node[0], k - 1, 0);
  // Node extract2 = utils::mkExtract(node[1], k - 1, 0);
  // Node k_zeroes = utils::mkConst(n - k, 0u);

  // NodeManager *nm = NodeManager::currentNM();
  // Node new_mult = nm->mkNode(kind::BITVECTOR_MULT, extract1, extract2);
  // Node result = utils::mkExtract(nm->mkNode(kind::BITVECTOR_CONCAT, k_zeroes, new_mult), high, low);

  // since the extract is over multiplier bits that have to be 0, return 0
  Node result = utils::mkConst(bitwidth, 0u); 
  //  std::cout << "MultLeadingBit " << node <<" => " << result <<"\n";
  return result;
  */
}

/* -------------------------------------------------------------------------- */

/**
 * NegIdemp
 *
 * -(-a) ==> a 
 */

template<> inline
bool RewriteRule<NegIdemp>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<NegIdemp>::apply(TNode node) {
  return rules::NegIdemp(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UdivPow2 
 *
 * (a udiv 2^k) ==> 0_k a[n-1: k]
 */

template <>
inline bool RewriteRule<UdivPow2>::applies(TNode node)
{
  return true;
  /*
  bool isNeg = false;
  if (node.getKind() == kind::BITVECTOR_UDIV_TOTAL
      && utils::isPow2Const(node[1], isNeg))
  {
    return !isNeg;
  }
  return false;
  */
}

template <>
inline Node RewriteRule<UdivPow2>::apply(TNode node)
{
  return rules::UdivPowX(node).d_node;
  /*
  Debug("bv-rewrite") << "RewriteRule<UdivPow2>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  unsigned size = utils::getSize(node);
  Node a = node[0];
  bool isNeg = false;
  unsigned power = utils::isPow2Const(node[1], isNeg) - 1;
  Node ret;
  if (power == 0)
  {
    ret = a;
  }
  else
  {
    Node extract = utils::mkExtract(a, size - 1, power);
    Node zeros = utils::mkConst(power, 0);

    ret = nm->mkNode(kind::BITVECTOR_CONCAT, zeros, extract);
  }
  if (isNeg && size > 1)
  {
    ret = nm->mkNode(kind::BITVECTOR_NEG, ret);
  }
  return ret;
  */
}

/* -------------------------------------------------------------------------- */

/**
 * UdivZero
 *
 * (a udiv 0) ==> 111...1
 */

template <>
inline bool RewriteRule<UdivZero>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<UdivZero>::apply(TNode node) {
  return rules::UdivZero(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UdivOne
 *
 * (a udiv 1) ==> a
 */

template <>
inline bool RewriteRule<UdivOne>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<UdivOne>::apply(TNode node) {
  return rules::UdivOne(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UremPow2
 *
 * (a urem 2^k) ==> 0_(n-k) a[k-1:0]
 */

template <>
inline bool RewriteRule<UremPow2>::applies(TNode node)
{
  return true;
}

template <>
inline Node RewriteRule<UremPow2>::apply(TNode node)
{
  return rules::UremPowX(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UremOne
 *
 * (a urem 1) ==> 0
 */

template<> inline
bool RewriteRule<UremOne>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<UremOne>::apply(TNode node) {
  return rules::UremOne(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * UremSelf 
 *
 * (a urem a) ==> 0
 */

template<> inline
bool RewriteRule<UremSelf>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<UremSelf>::apply(TNode node) {
  return rules::UremSelf(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * ShiftZero
 *
 * (0_k >> a) ==> 0_k 
 */

template<> inline
bool RewriteRule<ShiftZero>::applies(TNode node) {
  return ((node.getKind() == kind::BITVECTOR_SHL ||
           node.getKind() == kind::BITVECTOR_LSHR ||
           node.getKind() == kind::BITVECTOR_ASHR) &&
          node[0] == utils::mkConst(utils::getSize(node), 0));
}

template<> inline
Node RewriteRule<ShiftZero>::apply(TNode node) {
  Node n1 = rules::ShiftZeroShl(node).d_node;
  Node n2 = rules::ShiftZeroLshr(n1).d_node;
  return rules::ShiftZeroAshr(n2).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * BBPlusNeg
 * 
 * -a1 - a2 - ... - an + ak + ..  ==> - (a1 + a2 + ... + an) + ak
 *
 */

template<> inline
bool RewriteRule<BBPlusNeg>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_PLUS) {
    return false; 
  }

  unsigned neg_count = 0; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i].getKind()== kind::BITVECTOR_NEG) {
      ++neg_count; 
    }
  }
  return neg_count > 1;
}

template <>
inline Node RewriteRule<BBPlusNeg>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<BBPlusNeg>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  std::vector<Node> children;
  unsigned neg_count = 0;
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    if (node[i].getKind() == kind::BITVECTOR_NEG)
    {
      ++neg_count;
      children.push_back(nm->mkNode(kind::BITVECTOR_NOT, node[i][0]));
    }
    else
    {
      children.push_back(node[i]);
    }
  }
  Assert(neg_count != 0);
  children.push_back(utils::mkConst(utils::getSize(node), neg_count));

  return utils::mkNaryNode(kind::BITVECTOR_PLUS, children);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MergeSignExtend>::applies(TNode node) {
  return true;
}

template<> inline
Node RewriteRule<MergeSignExtend>::apply(TNode node) {
  Node n1 = rules::MergeSignExtendSign(node).d_node;
  return rules::MergeSignExtendZero(n1).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroExtendEqConst
 *
 * Rewrite zero_extend(x^n, m) = c^n+m to
 *
 *   false         if c[n+m-1:n] != 0
 *   x = c[n-1:0]  otherwise.
 */
template <>
inline bool RewriteRule<ZeroExtendEqConst>::applies(TNode node) {
  return true;
}

template <>
inline Node RewriteRule<ZeroExtendEqConst>::apply(TNode node) {
  return rules::ZeroExtendEqConst(node).d_node;
}

/* -------------------------------------------------------------------------- */

/**
 * SignExtendEqConst
 *
 * Rewrite sign_extend(x^n, m) = c^n+m to
 *
 *   x = c[n-1:0]   if (c[n-1:n-1] == 0 && c[n+m-1:n] == 0) ||
 *                     (c[n-1:n-1] == 1 && c[n+m-1:n] == ~0)
 *   false          otherwise.
 */
template <>
inline bool RewriteRule<SignExtendEqConst>::applies(TNode node) {
  return true;
  /*
  return node.getKind() == kind::EQUAL &&
         ((node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND &&
           node[1].isConst()) ||
          (node[1].getKind() == kind::BITVECTOR_SIGN_EXTEND &&
           node[0].isConst()));
           */
}

template <>
inline Node RewriteRule<SignExtendEqConst>::apply(TNode node) {
  return rules::SignExtendEqConst(node).d_node;
  /*
  TNode t, c;
  if (node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND) {
    t = node[0][0];
    c = node[1];
  } else {
    t = node[1][0];
    c = node[0];
  }
  unsigned pos_msb_t = utils::getSize(t) - 1;
  BitVector c_hi =
      c.getConst<BitVector>().extract(utils::getSize(c) - 1, pos_msb_t);
  BitVector c_lo = c.getConst<BitVector>().extract(pos_msb_t, 0);
  BitVector zero = BitVector(c_hi.getSize(), Integer(0));

  if (c_hi == zero || c_hi == ~zero) {
    return NodeManager::currentNM()->mkNode(kind::EQUAL, t,
                                            utils::mkConst(c_lo));
  }
  return utils::mkFalse();
  */
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroExtendUltConst
 *
 * Rewrite zero_extend(x^n,m) < c^n+m to
 *
 *   x < c[n-1:0]   if c[n+m-1:n] == 0.
 *
 * Rewrite c^n+m < Rewrite zero_extend(x^n,m) to
 *
 *   c[n-1:0] < x   if c[n+m-1:n] == 0.
 */
template <>
inline bool RewriteRule<ZeroExtendUltConst>::applies(TNode node) {
  return true;
  /*
  if (node.getKind() == kind::BITVECTOR_ULT &&
      ((node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND &&
        node[1].isConst()) ||
       (node[1].getKind() == kind::BITVECTOR_ZERO_EXTEND &&
        node[0].isConst()))) {
    TNode t, c;
    bool is_lhs = node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND;
    if (is_lhs) {
      t = node[0][0];
      c = node[1];
    } else {
      t = node[1][0];
      c = node[0];
    }

    if (utils::getSize(t) == utils::getSize(c))
    {
      return false;
    }

    BitVector bv_c = c.getConst<BitVector>();
    BitVector c_hi = c.getConst<BitVector>().extract(utils::getSize(c) - 1,
                                                     utils::getSize(t));
    BitVector zero = BitVector(c_hi.getSize(), Integer(0));

    return c_hi == zero;
  }
  return false;
  */
}

template <>
inline Node RewriteRule<ZeroExtendUltConst>::apply(TNode node) {
  Node n1 = rules::ZeroExtendUltConstLhs(node).d_node;
  return rules::ZeroExtendUltConstRhs(n1).d_node;
  /*
  TNode t, c;
  bool is_lhs = node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND;
  if (is_lhs) {
    t = node[0][0];
    c = node[1];
  } else {
    t = node[1][0];
    c = node[0];
  }
  Node c_lo =
      utils::mkConst(c.getConst<BitVector>().extract(utils::getSize(t) - 1, 0));

  if (is_lhs) {
    return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULT, t, c_lo);
  }
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULT, c_lo, t);
  */
}

/* -------------------------------------------------------------------------- */

/**
 * SignExtendUltConst
 *
 * Rewrite sign_extend(x^n,m) < c^n+m to
 *
 *   x < c[n-1:0]   if (c <= (1 << (n - 1))) || (c >= (~0 << (n - 1)))
 *   x[n-1:n-1] = 0 if (1 << (n - 1)) < c <= (~0 << (n - 1)).
 *
 * Rewrite c^n+m < sign_extend(x^n,m) to
 *
 *   c[n-1:0] < x   if (c < (1 << (n - 1))) || (c >= ~(1 << (n-1)))
 *   x[n-1:n-1] = 1 if ~(~0 << (n-1)) <= c <= ~(1 << (n-1))
 *
 * where ~(~0 << (n - 1)) == (1 << (n - 1)) - 1
 *
 */
template <>
inline bool RewriteRule<SignExtendUltConst>::applies(TNode node)
{
  return true;
  /*
  if (node.getKind() == kind::BITVECTOR_ULT
      && ((node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND
           && node[1].isConst())
          || (node[1].getKind() == kind::BITVECTOR_SIGN_EXTEND
              && node[0].isConst())))
  {
    TNode x, c;
    bool is_lhs = node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND;
    if (is_lhs)
    {
      x = node[0][0];
      c = node[1];
    }
    else
    {
      x = node[1][0];
      c = node[0];
    }
    BitVector bv_c = c.getConst<BitVector>();
    unsigned size_c = utils::getSize(c);
    unsigned msb_x_pos = utils::getSize(x) - 1;
    // (1 << (n - 1)))
    BitVector bv_msb_x = BitVector(size_c).setBit(msb_x_pos);
    // (~0 << (n - 1))
    BitVector bv_upper_bits =
        (~BitVector(size_c)).leftShift(BitVector(size_c, msb_x_pos));

    return (is_lhs
            && (bv_c <= bv_msb_x || bv_c >= bv_upper_bits
                || (bv_msb_x < bv_c && bv_c <= bv_upper_bits)))
           || (!is_lhs
               && (bv_c < bv_msb_x || bv_c >= ~bv_msb_x
                   || (~bv_upper_bits <= bv_c && bv_c <= ~bv_msb_x)));
  }
  return false;
  */
}

template <>
inline Node RewriteRule<SignExtendUltConst>::apply(TNode node)
{
  Node n1 = rules::SignExtendUltConstLhs(node).d_node;
  return rules::SignExtendUltConstRhs(n1).d_node;
  /*
  TNode x, c;
  bool is_lhs = node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND;
  if (is_lhs)
  {
    x = node[0][0];
    c = node[1];
  }
  else
  {
    x = node[1][0];
    c = node[0];
  }
  BitVector bv_c = c.getConst<BitVector>();

  unsigned size_c = utils::getSize(c);
  unsigned msb_x_pos = utils::getSize(x) - 1;
  Node c_lo = utils::mkConst(bv_c.extract(msb_x_pos, 0));
  // (1 << (n - 1)))
  BitVector bv_msb_x = BitVector(size_c).setBit(msb_x_pos);
  // (~0 << (n - 1))
  BitVector bv_upper_bits =
      (~BitVector(size_c)).leftShift(BitVector(size_c, msb_x_pos));

  NodeManager* nm = NodeManager::currentNM();
  if (is_lhs)
  {
    // x[n-1:n-1] = 0
    if (bv_msb_x < bv_c && bv_c <= bv_upper_bits)
    {
      Node msb_x = utils::mkExtract(x, msb_x_pos, msb_x_pos);
      return nm->mkNode(kind::EQUAL, msb_x, utils::mkZero(1));
    }
    // x < c[n-1:0]
    Assert(bv_c <= bv_msb_x || bv_c >= bv_upper_bits);
    return nm->mkNode(kind::BITVECTOR_ULT, x, c_lo);
  }

  // x[n-1:n-1] = 1
  if (~bv_upper_bits <= bv_c && bv_c <= ~bv_msb_x)
  {
    Node msb_x = utils::mkExtract(x, msb_x_pos, msb_x_pos);
    return nm->mkNode(kind::EQUAL, msb_x, utils::mkOne(1));
  }
  // c[n-1:0] < x
  Assert(bv_c < bv_msb_x || bv_c >= ~bv_msb_x);
  return nm->mkNode(kind::BITVECTOR_ULT, c_lo, x);
  */
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MultSlice>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_MULT || node.getNumChildren() != 2) {
    return false; 
  }
  return utils::getSize(node[0]) % 2 == 0;
}

/** 
 * Expressses the multiplication in terms of the top and bottom
 * slices of the terms. Note increases circuit size, but could
 * lead to simplifications (use wisely!).
 * 
 * @param node 
 * 
 * @return 
 */
template <>
inline Node RewriteRule<MultSlice>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<MultSlice>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  unsigned bitwidth = utils::getSize(node[0]);
  Node zeros = utils::mkConst(bitwidth / 2, 0);
  TNode a = node[0];
  Node bottom_a = utils::mkExtract(a, bitwidth / 2 - 1, 0);
  Node top_a = utils::mkExtract(a, bitwidth - 1, bitwidth / 2);
  TNode b = node[1];
  Node bottom_b = utils::mkExtract(b, bitwidth / 2 - 1, 0);
  Node top_b = utils::mkExtract(b, bitwidth - 1, bitwidth / 2);

  Node term1 = nm->mkNode(kind::BITVECTOR_MULT,
                          nm->mkNode(kind::BITVECTOR_CONCAT, zeros, bottom_a),
                          nm->mkNode(kind::BITVECTOR_CONCAT, zeros, bottom_b));

  Node term2 = nm->mkNode(kind::BITVECTOR_CONCAT,
                          nm->mkNode(kind::BITVECTOR_MULT, top_b, bottom_a),
                          zeros);
  Node term3 = nm->mkNode(kind::BITVECTOR_CONCAT,
                          nm->mkNode(kind::BITVECTOR_MULT, top_a, bottom_b),
                          zeros);
  return nm->mkNode(kind::BITVECTOR_PLUS, term1, term2, term3);
}

/* -------------------------------------------------------------------------- */

/** 
 * x < y + 1 <=> (not y < x) and y != 1...1
 * 
 * @param node 
 * 
 * @return 
 */
template<> inline
bool RewriteRule<UltPlusOne>::applies(TNode node) {
  return true; 
}

template <>
inline Node RewriteRule<UltPlusOne>::apply(TNode node)
{
  return rules::UltPlusOne(node).d_node;
}

/* -------------------------------------------------------------------------- */

/** 
 * x ^(x-1) = 0 => 1 << sk
 * WARNING: this is an **EQUISATISFIABLE** transformation!
 * Only to be called on top level assertions. 
 * 
 * @param node 
 * 
 * @return 
 */
template<> inline
bool RewriteRule<IsPowerOfTwo>::applies(TNode node) {
  if (node.getKind()!= kind::EQUAL) return false;
  if (node[0].getKind() != kind::BITVECTOR_AND &&
      node[1].getKind() != kind::BITVECTOR_AND)
    return false;
  if (!utils::isZero(node[0]) &&
      !utils::isZero(node[1]))
    return false;

  TNode t = !utils::isZero(node[0])? node[0]: node[1];
  if (t.getNumChildren() != 2) return false; 
  TNode a = t[0];
  TNode b = t[1];
  unsigned size = utils::getSize(t);
  if(size < 2) return false;
  Node diff = Rewriter::rewrite(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_SUB, a, b));
  return (diff.isConst() && (diff == utils::mkConst(size, 1u) || diff == utils::mkOnes(size)));
}

template <>
inline Node RewriteRule<IsPowerOfTwo>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<IsPowerOfTwo>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode term = utils::isZero(node[0]) ? node[1] : node[0];
  TNode a = term[0];
  TNode b = term[1];
  unsigned size = utils::getSize(term);
  Node diff = Rewriter::rewrite(nm->mkNode(kind::BITVECTOR_SUB, a, b));
  Assert(diff.isConst());
  TNode x = diff == utils::mkConst(size, 1u) ? a : b;
  Node one = utils::mkConst(size, 1u);
  Node sk = utils::mkVar(size);
  Node sh = nm->mkNode(kind::BITVECTOR_SHL, one, sk);
  Node x_eq_sh = nm->mkNode(kind::EQUAL, x, sh);
  return x_eq_sh;
}

/* -------------------------------------------------------------------------- */

/**
 * Rewrite
 *   sign_extend(x+t,n) * sign_extend(a,m) < sign_extend(x,n) * sign_extend(a,m)
 * to
 *   (and
 *    (not (= t zero))
 *    (not (= a zero))
 *    (= (bvslt (bvadd x t) x) (bvsgt a zero))
 *   )
 *
 * Rewrite
 *   zero_extend(x+t,n) * sign_extend(a,m) < zero_extend(x,n) * sign_extend(a,m)
 * to
 *   (and
 *    (not (= t zero))
 *    (not (= a zero))
 *    (= (bvult (bvadd x t) x) (bvsgt a zero))
 *   )
 * where n and m are sufficiently big to not produce an overflow for
 * the multiplications.
 *
 * These patterns occur in the quantified BV benchmark family 'ranking',
 * where the BV engine struggles due to the high bit widths of the
 * multiplication's operands.
 */
static std::tuple<Node, Node, bool>
extract_ext_tuple(TNode node)
{
  TNode a = node[0];
  TNode b = node[1];
  for (unsigned i = 0; i < 2; ++i)
  {
    if (a.getKind() == kind::BITVECTOR_CONCAT
        && b.getKind() == kind::BITVECTOR_SIGN_EXTEND
        && a[0] == utils::mkZero(utils::getSize(a[0]))
        && utils::getSize(a[1]) <= utils::getSize(a[0])
        && utils::getSize(b[0]) <= utils::getSignExtendAmount(b))
    {
      return std::make_tuple(a[1], b[0], false);
    }
    else if (i == 0
             && a.getKind() == kind::BITVECTOR_SIGN_EXTEND
             && b.getKind() == kind::BITVECTOR_SIGN_EXTEND
             && utils::getSize(a[0]) <= utils::getSignExtendAmount(a)
             && utils::getSize(b[0]) <= utils::getSignExtendAmount(b))
    {
      return std::make_tuple(a[0], b[0], true);
    }
    std::swap(a, b);
  }
  return std::make_tuple(Node::null(), Node::null(), false);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MultSltMult>::applies(TNode node)
{
  if (node.getKind() != kind::BITVECTOR_SLT
      || node[0].getKind() != kind::BITVECTOR_MULT
      || node[1].getKind() != kind::BITVECTOR_MULT)
    return false;

  if (node[0].getNumChildren() > 2 || node[1].getNumChildren() > 2)
    return false;

  bool is_sext_l, is_sext_r;
  TNode ml[2], mr[2];

  std::tie(ml[0], ml[1], is_sext_l) = extract_ext_tuple(node[0]);
  if (ml[0].isNull())
    return false;

  std::tie(mr[0], mr[1], is_sext_r) = extract_ext_tuple(node[1]);
  if (mr[0].isNull())
    return false;

  if (is_sext_l != is_sext_r)
    return false;

  TNode addxt, x, a;
  if (ml[0].getKind() == kind::BITVECTOR_PLUS)
  {
    addxt = ml[0];
    a = ml[1];
  }
  else if (ml[1].getKind() == kind::BITVECTOR_PLUS)
  {
    addxt = ml[1];
    a = ml[0];
  }
  else
    return false;

  if (addxt.getNumChildren() > 2)
    return false;

  if (mr[0] == a)
  {
    x = mr[1];
  }
  else if (mr[1] == a)
  {
    x = mr[0];
  }
  else
    return false;

  return (addxt[0] == x || addxt[1] == x);
}

template<> inline
Node RewriteRule<MultSltMult>::apply(TNode node)
{
  bool is_sext;
  TNode ml[2], mr[2];

  std::tie(ml[0], ml[1], is_sext) = extract_ext_tuple(node[0]);
  std::tie(mr[0], mr[1], std::ignore) = extract_ext_tuple(node[1]);

  TNode addxt, x, t, a;
  if (ml[0].getKind() == kind::BITVECTOR_PLUS)
  {
    addxt = ml[0];
    a = ml[1];
  }
  else
  {
    Assert(ml[1].getKind() == kind::BITVECTOR_PLUS);
    addxt = ml[1];
    a = ml[0];
  }

  x = (mr[0] == a) ? mr[1] : mr[0];
  t = (addxt[0] == x) ? addxt[1] : addxt[0];

  NodeManager *nm = NodeManager::currentNM();
  Node zero_t = utils::mkZero(utils::getSize(t));
  Node zero_a = utils::mkZero(utils::getSize(a));

  NodeBuilder<> nb(kind::AND);
  Kind k = is_sext ? kind::BITVECTOR_SLT : kind::BITVECTOR_ULT;
  nb << t.eqNode(zero_t).notNode();
  nb << a.eqNode(zero_a).notNode();
  nb << nm->mkNode(k, addxt, x)
            .eqNode(nm->mkNode(kind::BITVECTOR_SGT, a, zero_a));
  return nb.constructNode();
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
