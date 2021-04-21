/*********************                                                        */
/*! \file theory_bv_rewriter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for the bit-vector rewriter
 **
 ** Unit tests for the bit-vector rewriter.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <memory>
#include <vector>

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::smt;
using namespace CVC4::theory;

class TheoryBvRewriterWhite : public CxxTest::TestSuite
{
 public:
  TheoryBvRewriterWhite() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager(opts);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);

    d_nm = NodeManager::currentNM();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  Node boolToBv(Node b)
  {
    return d_nm->mkNode(ITE,
                        b,
                        d_nm->mkConst(BitVector(1, 1u)),
                        d_nm->mkConst(BitVector(1, 0u)));
  }

  void testShlByConst()
  {
    TypeNode bvType = d_nm->mkBitVectorType(4);

    Node zero = d_nm->mkConst(BitVector(4, Integer(0)));
    Node zero_2 = d_nm->mkConst(BitVector(2, Integer(0)));
    Node two = d_nm->mkConst(BitVector(4, Integer(2)));
    Node six = d_nm->mkConst(BitVector(4, Integer(6)));
    Node x = d_nm->mkVar("x", bvType);

    {
      // x << 0 ---> x
      Node n = d_nm->mkNode(BITVECTOR_SHL, x, zero);
      Node nr = Rewriter::rewrite(n);
      TS_ASSERT_EQUALS(nr, x);
    }

    {
      // x << 6 ---> 0
      Node n = d_nm->mkNode(BITVECTOR_SHL, x, six);
      Node nr = Rewriter::rewrite(n);
      TS_ASSERT_EQUALS(nr, zero);
    }

    {
      // x << 2 ---> concat(x[1:0], 0^2)
      Node n = d_nm->mkNode(BITVECTOR_SHL, x, two);
      Node nr = Rewriter::rewrite(n);
      Node expected = d_nm->mkNode(BITVECTOR_CONCAT, d_nm->mkNode(d_nm->mkConst<BitVectorExtract>(BitVectorExtract(1, 0)), x), zero_2);
      TS_ASSERT_EQUALS(nr, Rewriter::rewrite(expected));
    }
  }

  void testLshrByConst()
  {
    TypeNode bvType = d_nm->mkBitVectorType(4);

    Node zero = d_nm->mkConst(BitVector(4, Integer(0)));
    Node zero_2 = d_nm->mkConst(BitVector(2, Integer(0)));
    Node two = d_nm->mkConst(BitVector(4, Integer(2)));
    Node six = d_nm->mkConst(BitVector(4, Integer(6)));
    Node x = d_nm->mkVar("x", bvType);

    {
      // x >> 0 ---> x
      Node n = d_nm->mkNode(BITVECTOR_LSHR, x, zero);
      Node nr = Rewriter::rewrite(n);
      TS_ASSERT_EQUALS(nr, x);
    }

    {
      // x >> 6 ---> 0
      Node n = d_nm->mkNode(BITVECTOR_LSHR, x, six);
      Node nr = Rewriter::rewrite(n);
      TS_ASSERT_EQUALS(nr, zero);
    }

    {
      // x >> 2 ---> concat(0^2, x[1:0])
      Node n = d_nm->mkNode(BITVECTOR_LSHR, x, two);
      Node nr = Rewriter::rewrite(n);
      Node expected = d_nm->mkNode(BITVECTOR_CONCAT, zero_2, d_nm->mkNode(d_nm->mkConst<BitVectorExtract>(BitVectorExtract(3, 2)), x));
      TS_ASSERT_EQUALS(nr, Rewriter::rewrite(expected));
    }
  }

  void testAshrByConst()
  {
    TypeNode bvType = d_nm->mkBitVectorType(4);

    Node zero = d_nm->mkConst(BitVector(4, Integer(0)));
    Node zero_2 = d_nm->mkConst(BitVector(2, Integer(0)));
    Node two = d_nm->mkConst(BitVector(4, Integer(2)));
    Node six = d_nm->mkConst(BitVector(4, Integer(6)));
    Node x = d_nm->mkVar("x", bvType);

    {
      // x >>_a 0 ---> x
      Node n = d_nm->mkNode(BITVECTOR_ASHR, x, zero);
      Node nr = Rewriter::rewrite(n);
      TS_ASSERT_EQUALS(nr, x);
    }

    {
      // x >>_a 6 ---> repeat_4(x[3])
      Node n = d_nm->mkNode(BITVECTOR_ASHR, x, six);
      Node nr = Rewriter::rewrite(n);
      Node expected = d_nm->mkNode(d_nm->mkConst<BitVectorRepeat>(BitVectorRepeat(4)), d_nm->mkNode(d_nm->mkConst<BitVectorExtract>(BitVectorExtract(3, 3)), x));
      TS_ASSERT_EQUALS(nr, Rewriter::rewrite(expected));
    }

    {
      // x >>_ 2 ---> concat(repeat_2(x[3]), x[3:2]))
      Node n = d_nm->mkNode(BITVECTOR_ASHR, x, two);
      Node nr = Rewriter::rewrite(n);
      Node expected = d_nm->mkNode(BITVECTOR_CONCAT, d_nm->mkNode(d_nm->mkConst<BitVectorRepeat>(BitVectorRepeat(2)), d_nm->mkNode(d_nm->mkConst<BitVectorExtract>(BitVectorExtract(3, 3)), x)), d_nm->mkNode(d_nm->mkConst<BitVectorExtract>(BitVectorExtract(3, 2)), x));
      TS_ASSERT_EQUALS(nr, Rewriter::rewrite(expected));
    }
  }

  void testMultDistrib()
  {
    TypeNode bvType = d_nm->mkBitVectorType(4);

    Node zero = d_nm->mkConst(BitVector(4, Integer(0)));
    Node zero_2 = d_nm->mkConst(BitVector(2, Integer(0)));
    Node two = d_nm->mkConst(BitVector(4, Integer(2)));
    Node six = d_nm->mkConst(BitVector(4, Integer(6)));
    Node x = d_nm->mkVar("x", bvType);

    {
    }
  }

  void testRewriteToFixpoint()
  {
    TypeNode boolType = d_nm->booleanType();
    TypeNode bvType = d_nm->mkBitVectorType(1);

    Node zero = d_nm->mkConst(BitVector(1, 0u));
    Node b1 = d_nm->mkVar("b1", boolType);
    Node b2 = d_nm->mkVar("b2", boolType);
    Node b3 = d_nm->mkVar("b3", boolType);
    Node bv = d_nm->mkVar("bv", bvType);

    Node n = d_nm->mkNode(
        BITVECTOR_ITE,
        boolToBv(b1),
        d_nm->mkNode(BITVECTOR_ITE,
                     boolToBv(b2),
                     d_nm->mkNode(BITVECTOR_ITE, boolToBv(b3), zero, bv),
                     bv),
        bv);
    Node nr = Rewriter::rewrite(n);
    TS_ASSERT_EQUALS(nr, Rewriter::rewrite(nr));
  }

  void testRewriteBvIte()
  {
    TypeNode boolType = d_nm->booleanType();
    TypeNode bvType = d_nm->mkBitVectorType(1);

    Node zero = d_nm->mkConst(BitVector(1, 0u));
    Node c1 = d_nm->mkVar("c1", bvType);
    Node c2 = d_nm->mkVar("c2", bvType);

    Node ite = d_nm->mkNode(BITVECTOR_ITE, c2, zero, zero);
    Node n = d_nm->mkNode(BITVECTOR_ITE, c1, ite, ite);
    Node nr = Rewriter::rewrite(n);
    TS_ASSERT_EQUALS(nr, Rewriter::rewrite(nr));
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;

  NodeManager* d_nm;
};
