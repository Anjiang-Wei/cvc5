/*********************                                                        */
/*! \file skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a cache of skolems for theory of strings.
 **/

#include "theory/strings/skolem_cache.h"

#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/rational.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

SkolemCache::SkolemCache()
{
  NodeManager* nm = NodeManager::currentNM();
  d_strType = nm->stringType();
  d_zero = nm->mkConst(Rational(0));
}

Node SkolemCache::mkSkolemCached(Node a, Node b, Node c, SkolemId id, const char* name)
{
  return mkTypedSkolemCached(d_strType, a, b, c, id, name);
}

Node SkolemCache::mkSkolemCached(Node a, Node b, SkolemId id, const char* name)
{
  return mkTypedSkolemCached(d_strType, a, b, Node::null(), id, name);
}

Node SkolemCache::mkSkolemCached(Node a, SkolemId id, const char* name)
{
  return mkSkolemCached(a, Node::null(), Node::null(), id, name);
}

Node SkolemCache::mkTypedSkolemCached(
    TypeNode tn, Node a, Node b, Node c, SkolemId id, const char* name)
{
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);
  c = c.isNull() ? c : Rewriter::rewrite(c);

  if (options::skolemSharing() && tn == d_strType)
  {
    std::tie(id, a, b, c) = normalizeStringSkolem(id, a, b, c);
  }

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b][c].find(id);
  if (it == d_skolemCache[a][b][c].end())
  {
    Node sk = mkTypedSkolem(tn, name);
    d_skolemCache[a][b][c][id] = sk;
    return sk;
  }
  return it->second;
}
Node SkolemCache::mkTypedSkolemCached(TypeNode tn,
                                      Node a,
                                      SkolemId id,
                                      const char* name)
{
  return mkTypedSkolemCached(tn, a, Node::null(), Node::null(), id, name);
}

Node SkolemCache::mkSkolem(const char* name)
{
  return mkTypedSkolem(d_strType, name);
}

Node SkolemCache::mkTypedSkolem(TypeNode tn, const char* name)
{
  Node n = NodeManager::currentNM()->mkSkolem(name, tn, "string skolem");
  d_allSkolems.insert(n);
  return n;
}

bool SkolemCache::isSkolem(Node n) const
{
  return d_allSkolems.find(n) != d_allSkolems.end();
}

std::tuple<SkolemCache::SkolemId, Node, Node, Node>
SkolemCache::normalizeStringSkolem(SkolemId id, Node a, Node b, Node c)
{
  Trace("skolem-cache") << "normalizeStringSkolem start: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  if (id == SK_FIRST_CTN_IOPRE || id == SK_FIRST_CTN_RFCPRE)
  {
    id = SK_FIRST_CTN_PRE;
  }
  else if (id == SK_FIRST_CTN_IOPOST || id == SK_FIRST_CTN_RFCPOST)
  {
    id = SK_FIRST_CTN_POST;
  }
  else if (id == SK_REGEXP_CONCAT)
  {
    Node curr = b.getKind() == REGEXP_CONCAT ? b[b.getNumChildren() - 1] : b;
    Node len = TheoryStringsRewriter::getFixedLengthForRegexp(curr);
    if (!len.isNull())
    {
      if (b.getKind() != REGEXP_CONCAT)
      {
        id = SK_PREFIX;
        b = len;
        c = Node::null();
      }
      else if (c == nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String(""))))
      {
        id = SK_SUFFIX_REM;
        b = nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, a), len);
        c = Node::null();
      }
      else
      {
        std::vector<Node> vprefix(b.begin(), b.end() - 1);
        Node prefix = utils::mkConcat(REGEXP_CONCAT, vprefix);
        Node plen = TheoryStringsRewriter::getFixedLengthForRegexp(prefix);
        Node slen = TheoryStringsRewriter::getFixedLengthForRegexp(c);
        if (!plen.isNull())
        {
          id = SK_SUFFIX_REM;
          a = mkSkolemCached(a, nm->mkNode(PLUS, len, plen), SK_PREFIX, "pre");
          b = plen;
          c = Node::null();
        }
        else if (!slen.isNull())
        {
          id = SK_PREFIX;
          a = mkSkolemCached(a,
                             nm->mkNode(MINUS,
                                        nm->mkNode(STRING_LENGTH, a),
                                        nm->mkNode(PLUS, slen, len)),
                             SK_SUFFIX_REM,
                             "suf");
          b = plen;
          c = Node::null();
        }
      }
    }
  }

  if (id == SK_FIRST_CTN_POST)
  {
    // SK_FIRST_CTN_POST(x, y) --->
    //   SK_SUFFIX_REM(x, (+ (str.len SK_FIRST_CTN_PRE(x, y)) (str.len y)))
    id = SK_SUFFIX_REM;
    Node pre = mkSkolemCached(a, b, SK_FIRST_CTN_PRE, "pre");
    b = Rewriter::rewrite(nm->mkNode(
        PLUS, nm->mkNode(STRING_LENGTH, pre), nm->mkNode(STRING_LENGTH, b)));
  }

  if (id == SK_ID_C_SPT)
  {
    // SK_ID_C_SPT(x, y) ---> SK_SUFFIX_REM(x, (str.len y))
    id = SK_SUFFIX_REM;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SK_ID_C_SPT_REV)
  {
    // SK_ID_C_SPT_REV(x, y) ---> SK_PREFIX(x, (- (str.len x) (str.len y)))
    id = SK_PREFIX;
    b = Rewriter::rewrite(nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkNode(STRING_LENGTH, b)));
  }
  else if (id == SK_ID_VC_SPT)
  {
    // SK_ID_VC_SPT(x, y) ---> SK_SUFFIX_REM(x, 1)
    id = SK_SUFFIX_REM;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SK_ID_VC_SPT_REV)
  {
    // SK_ID_VC_SPT_REV(x, y) ---> SK_PREFIX(x, (- (str.len x) 1))
    id = SK_PREFIX;
    b = Rewriter::rewrite(nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkConst(Rational(1))));
  }
  else if (id == SK_ID_DC_SPT)
  {
    // SK_ID_DC_SPT(x, y) ---> SK_PREFIX(x, 1)
    id = SK_PREFIX;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SK_ID_V_SPT_X)
  {
    // SK_ID_V_SPT_X(x, y) ---> SK_SUFFIX_REM(a, (str.len b))
    id = SK_SUFFIX_REM;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SK_ID_V_SPT_REV_X)
  {
    // SK_ID_V_SPT_REV_X(x, y) ---> SK_PREFIX(a, (- (str.len a) (str.len b)))
    id = SK_PREFIX;
    b = Rewriter::rewrite(nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkNode(STRING_LENGTH, b)));
  }
  else if (id == SK_ID_V_SPT_Y)
  {
    // SK_ID_V_SPT_Y(x, y) ---> SK_SUFFIX_REM(b, (str.len a))
    id = SK_SUFFIX_REM;
    Node aOld = a;
    a = b;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, aOld));
  }
  else if (id == SK_ID_V_SPT_REV_Y)
  {
    // SK_ID_V_SPT_REV_Y(x, y) ---> SK_PREFIX(b, (- (str.len b) (str.len a)))
    id = SK_PREFIX;
    Node aOld = a;
    a = b;
    b = Rewriter::rewrite(nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, b), nm->mkNode(STRING_LENGTH, aOld)));
  }
  else if (id == SK_ID_DC_SPT_REM)
  {
    // SK_ID_DC_SPT_REM(x, y) ---> SK_SUFFIX_REM(x, 1)
    id = SK_SUFFIX_REM;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SK_ID_DEQ_X)
  {
    // SK_ID_DEQ_X(x, y) ---> SK_PREFIX(y, (str.len x))
    id = SK_PREFIX;
    Node aOld = a;
    a = b;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, aOld));
  }
  else if (id == SK_ID_DEQ_Y)
  {
    // SK_ID_DEQ_Y(x, y) ---> SK_PREFIX(x, (str.len y))
    id = SK_PREFIX;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SK_ID_DEQ_Z)
  {
    // SK_ID_DEQ_Z(x, y) ---> SK_SUFFIX_REM(y, (str.len x))
    id = SK_SUFFIX_REM;
    Node aOld = a;
    a = b;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, aOld));
  }
  else if (id == SK_ID_DEQ_W)
  {
    // SK_ID_DEQ_W(x, y) ---> SK_SUFFIX_REM(x, (str.len y))
    id = SK_SUFFIX_REM;
    b = Rewriter::rewrite(nm->mkNode(STRING_LENGTH, b));
  }

  if (id == SK_STAR_PREFIX)
  {
    Node len = TheoryStringsRewriter::getFixedLengthForRegexp(b);
    if (!len.isNull())
    {
      id = SK_PREFIX;
      b = len;
    }
  }
  else if (id == SK_STAR_MID)
  {
    Node len = TheoryStringsRewriter::getFixedLengthForRegexp(b);
    if (!len.isNull())
    {
      id = SK_PURIFY;
      a = nm->mkNode(
          STRING_SUBSTR,
          a,
          len,
          nm->mkNode(
              MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkNode(PLUS, len, len)));
      b = Node::null();
    }
  }
  else if (id == SK_STAR_SUFFIX)
  {
    Node len = TheoryStringsRewriter::getFixedLengthForRegexp(b);
    if (!len.isNull())
    {
      id = SK_SUFFIX_REM;
      b = Rewriter::rewrite(
          nm->mkNode(MINUS, nm->mkNode(STRING_LENGTH, a), len));
    }
  }

  if (id == SK_PURIFY && a.getKind() == kind::STRING_SUBSTR)
  {
    Node s = a[0];
    Node n = a[1];
    Node m = a[2];

    if (n == d_zero)
    {
      // SK_PURIFY((str.substr x 0 m)) ---> SK_PREFIX(x, m)
      id = SK_PREFIX;
      a = s;
      b = m;
    }
    else if (TheoryStringsRewriter::checkEntailArith(
                 nm->mkNode(PLUS, n, m), nm->mkNode(STRING_LENGTH, s)))
    {
      // SK_PURIFY((str.substr x n m)) ---> SK_SUFFIX_REM(x, n)
      // if n + m >= (str.len x)
      id = SK_SUFFIX_REM;
      a = s;
      b = n;
    }
  }

  if (id == SK_PREFIX && b.getKind() == kind::STRING_STRIDOF && a == b[0]
      && b[2] == d_zero)
  {
    // SK_PREFIX(x, (str.indexof x y 0)) ---> SK_FIRST_CTN_PRE(x, y)
    id = SK_FIRST_CTN_PRE;
    b = b[1];
  }

  if (id == SK_FIRST_CTN_PRE)
  {
    // SK_FIRST_CTN_PRE((str.substr x 0 n), y) ---> SK_FIRST_CTN_PRE(x, y)
    while (a.getKind() == kind::STRING_SUBSTR && a[1] == d_zero)
    {
      a = a[0];
    }
  }

  Trace("skolem-cache") << "normalizeStringSkolem end: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  return std::make_tuple(id, a, b, c);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
