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
#include "theory/strings/arith_entail.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

SkolemCache::SkolemCache(SequencesStatistics& statistics, bool useOpts)
    : d_statistics(statistics), d_useOpts(useOpts)
{
  NodeManager* nm = NodeManager::currentNM();
  d_strType = nm->stringType();
  d_zero = nm->mkConst(Rational(0));
}

Node SkolemCache::mkSkolemCached(Node a, Node b, SkolemId id, const char* c)
{
  return mkTypedSkolemCached(d_strType, a, b, id, c);
}

Node SkolemCache::mkSkolemCached(Node a, SkolemId id, const char* c)
{
  return mkSkolemCached(a, Node::null(), id, c);
}

Node SkolemCache::mkTypedSkolemCached(
    TypeNode tn, Node a, Node b, SkolemId id, const char* c)
{
  Trace("skolem-cache") << "mkTypedSkolemCached start: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  SkolemId idOrig = id;
  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  if (d_skolemCachePreOnly[a][b].find(id) == d_skolemCachePreOnly[a][b].end())
  {
    d_skolemCachePreOnly[a][b][id] = Node::null();
    d_statistics.d_numCachedSkolemsPre << id;
  }

  if (options::skolemSharing())
  {
    std::tie(id, a, b) = normalizeStringSkolem(id, a, b);
  }

  // optimization: if we aren't asking for the purification skolem for constant
  // a, and the skolem is equivalent to a, then we just return a.
  if (d_useOpts && idOrig != SkolemId::SK_PURIFY && id == SkolemId::SK_PURIFY
      && a.isConst())
  {
    Trace("skolem-cache") << "...optimization: return constant " << a
                          << std::endl;
    return a;
  }

  std::map<SkolemId, Node>::iterator it = d_skolemCache[a][b].find(id);
  if (it == d_skolemCache[a][b].end())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node sk;
    if (options::skolemSharing())
    {
      switch (id)
      {
        // exists k. k = a
        case SkolemId::SK_PURIFY:
          sk = d_pskc.mkPurifySkolem(a, c, "string purify skolem");
          break;
        // these are eliminated by normalizeStringSkolem
        case SkolemId::SK_ID_V_SPT:
        case SkolemId::SK_ID_V_SPT_REV:
        case SkolemId::SK_ID_VC_SPT:
        case SkolemId::SK_ID_VC_SPT_REV:
        case SkolemId::SK_FIRST_CTN_POST:
        case SkolemId::SK_ID_C_SPT:
        case SkolemId::SK_ID_C_SPT_REV:
        case SkolemId::SK_ID_DC_SPT:
        case SkolemId::SK_ID_DC_SPT_REM:
        case SkolemId::SK_ID_DEQ_X:
        case SkolemId::SK_ID_DEQ_Y:
        case SkolemId::SK_FIRST_CTN_PRE:
        case SkolemId::SK_PREFIX:
        case SkolemId::SK_SUFFIX_REM:
          Unhandled() << "Expected to eliminate Skolem ID " << id << std::endl;
          break;
        case SkolemId::SK_NUM_OCCUR:
        case SkolemId::SK_OCCUR_INDEX:
        default:
        {
          Notice() << "Don't know how to handle Skolem ID " << id << std::endl;
          Node v = nm->mkBoundVar(tn);
          Node cond = nm->mkConst(true);
          sk = d_pskc.mkSkolem(v, cond, c, "string skolem");
        }
        break;
      }
    }
    else
    {
      Node v = nm->mkBoundVar(tn);
      Node cond = nm->mkConst(true);
      sk = d_pskc.mkSkolem(v, cond, c, "string skolem");
    }
    d_allSkolems.insert(sk);
    d_skolemCache[a][b][id] = sk;
    d_statistics.d_numCachedSkolemsPost << idOrig;
    return sk;
  }
  return it->second;
}
Node SkolemCache::mkTypedSkolemCached(TypeNode tn,
                                      Node a,
                                      SkolemId id,
                                      const char* c)
{
  return mkTypedSkolemCached(tn, a, Node::null(), id, c);
}

Node SkolemCache::mkSkolem(const char* c)
{
  // TODO: eliminate this
  Node n = NodeManager::currentNM()->mkSkolem(c, d_strType, "string skolem");
  d_allSkolems.insert(n);
  return n;
}

bool SkolemCache::isSkolem(Node n) const
{
  return d_allSkolems.find(n) != d_allSkolems.end();
}

std::tuple<SkolemId, Node, Node> SkolemCache::normalizeStringSkolem(SkolemId id,
                                                                    Node a,
                                                                    Node b)
{
  NodeManager* nm = NodeManager::currentNM();

  if (id == SkolemId::SK_FIRST_CTN_IOPRE || id == SkolemId::SK_FIRST_CTN_RFCPRE)
  {
    id = SkolemId::SK_FIRST_CTN_PRE;
  }
  else if (id == SkolemId::SK_FIRST_CTN_IOPOST
           || id == SkolemId::SK_FIRST_CTN_RFCPOST)
  {
    id = SkolemId::SK_FIRST_CTN_POST;
  }

  // eliminate in terms of prefix/suffix_rem
  if (id == SkolemId::SK_FIRST_CTN_POST)
  {
    // SK_FIRST_CTN_POST(x, y) --->
    //   SK_SUFFIX_REM(x, (+ (str.len SK_FIRST_CTN_PRE(x, y)) (str.len y)))
    id = SkolemId::SK_SUFFIX_REM;
    Node pre = mkSkolemCached(a, b, SkolemId::SK_FIRST_CTN_PRE, "pre");
    b = nm->mkNode(
        PLUS, nm->mkNode(STRING_LENGTH, pre), nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SkolemId::SK_ID_V_SPT || id == SkolemId::SK_ID_C_SPT)
  {
    // SK_ID_*_SPT(x, y) ---> SK_SUFFIX_REM(x, (str.len y))
    id = SkolemId::SK_SUFFIX_REM;
    b = nm->mkNode(STRING_LENGTH, b);
  }
  else if (id == SkolemId::SK_ID_V_SPT_REV || id == SkolemId::SK_ID_C_SPT_REV)
  {
    // SK_ID_*_SPT_REV(x, y) ---> SK_PREFIX(x, (- (str.len x) (str.len y)))
    id = SkolemId::SK_PREFIX;
    b = nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkNode(STRING_LENGTH, b));
  }
  else if (id == SkolemId::SK_ID_VC_SPT)
  {
    // SK_ID_VC_SPT(x, y) ---> SK_SUFFIX_REM(x, 1)
    id = SkolemId::SK_SUFFIX_REM;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SkolemId::SK_ID_VC_SPT_REV)
  {
    // SK_ID_VC_SPT_REV(x, y) ---> SK_PREFIX(x, (- (str.len x) 1))
    id = SkolemId::SK_PREFIX;
    b = nm->mkNode(
        MINUS, nm->mkNode(STRING_LENGTH, a), nm->mkConst(Rational(1)));
  }
  else if (id == SkolemId::SK_ID_DC_SPT)
  {
    // SK_ID_DC_SPT(x, y) ---> SK_PREFIX(x, 1)
    id = SkolemId::SK_PREFIX;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SkolemId::SK_ID_DC_SPT_REM)
  {
    // SK_ID_DC_SPT_REM(x, y) ---> SK_SUFFIX_REM(x, 1)
    id = SkolemId::SK_SUFFIX_REM;
    b = nm->mkConst(Rational(1));
  }
  else if (id == SkolemId::SK_ID_DEQ_X)
  {
    // SK_ID_DEQ_X(x, y) ---> SK_PREFIX(y, (str.len x))
    id = SkolemId::SK_PREFIX;
    Node aOld = a;
    a = b;
    b = nm->mkNode(STRING_LENGTH, aOld);
  }
  else if (id == SkolemId::SK_ID_DEQ_Y)
  {
    // SK_ID_DEQ_Y(x, y) ---> SK_PREFIX(x, (str.len y))
    id = SkolemId::SK_PREFIX;
    b = nm->mkNode(STRING_LENGTH, b);
  }
  else if (id == SkolemId::SK_FIRST_CTN_PRE)
  {
    // SK_FIRST_CTN_PRE(x,y) ---> SK_PREFIX(x, indexof(x,y,0))
    id = SkolemId::SK_PREFIX;
    b = nm->mkNode(STRING_STRIDOF, a, b, d_zero);
  }

  if (id == SkolemId::SK_ID_V_UNIFIED_SPT
      || id == SkolemId::SK_ID_V_UNIFIED_SPT_REV)
  {
    bool isRev = (id == SkolemId::SK_ID_V_UNIFIED_SPT_REV);
    Node la = nm->mkNode(STRING_LENGTH, a);
    Node lb = nm->mkNode(STRING_LENGTH, b);
    Node ta = isRev ? utils::mkPrefix(a, nm->mkNode(MINUS, la, lb))
                    : utils::mkSuffix(a, lb);
    Node tb = isRev ? utils::mkPrefix(b, nm->mkNode(MINUS, lb, la))
                    : utils::mkSuffix(b, la);
    id = SkolemId::SK_PURIFY;
    a = nm->mkNode(ITE, nm->mkNode(GEQ, la, lb), ta, tb);
    b = Node::null();
  }

  // now, eliminate prefix/suffix_rem in terms of purify
  if (id == SkolemId::SK_PREFIX)
  {
    // SK_PREFIX(x,y) ---> SK_PURIFY(substr(x,0,y))
    id = SkolemId::SK_PURIFY;
    a = utils::mkPrefix(a, b);
    b = Node::null();
  }
  else if (id == SkolemId::SK_SUFFIX_REM)
  {
    // SK_SUFFIX_REM(x,y) ---> SK_PURIFY(substr(x,y,str.len(x)-y))
    id = SkolemId::SK_PURIFY;
    a = utils::mkSuffix(a, b);
    b = Node::null();
  }

  a = a.isNull() ? a : Rewriter::rewrite(a);
  b = b.isNull() ? b : Rewriter::rewrite(b);

  Trace("skolem-cache") << "normalizeStringSkolem end: (" << id << ", " << a
                        << ", " << b << ")" << std::endl;
  return std::make_tuple(id, a, b);
}

const char* toString(SkolemId id)
{
  switch (id)
  {
    case SkolemId::SK_PURIFY: return "SK_PURIFY";
    case SkolemId::SK_ID_C_SPT: return "SK_ID_C_SPT";
    case SkolemId::SK_ID_C_SPT_REV: return "SK_ID_C_SPT_REV";
    case SkolemId::SK_ID_VC_SPT: return "SK_ID_VC_SPT";
    case SkolemId::SK_ID_VC_SPT_REV: return "SK_ID_VC_SPT_REV";
    case SkolemId::SK_ID_V_SPT: return "SK_ID_V_SPT";
    case SkolemId::SK_ID_V_SPT_REV: return "SK_ID_V_SPT_REV";
    case SkolemId::SK_ID_V_UNIFIED_SPT: return "SK_ID_V_UNIFIED_SPT";
    case SkolemId::SK_ID_V_UNIFIED_SPT_REV: return "SK_ID_V_UNIFIED_SPT_REV";
    case SkolemId::SK_ID_DC_SPT: return "SK_ID_DC_SPT";
    case SkolemId::SK_ID_DC_SPT_REM: return "SK_ID_DC_SPT_REM";
    case SkolemId::SK_ID_DEQ_X: return "SK_ID_DEQ_X";
    case SkolemId::SK_ID_DEQ_Y: return "SK_ID_DEQ_Y";
    case SkolemId::SK_FIRST_CTN_PRE: return "SK_FIRST_CTN_PRE";
    case SkolemId::SK_FIRST_CTN_POST: return "SK_FIRST_CTN_POST";
    case SkolemId::SK_FIRST_CTN_IOPRE: return "SK_FIRST_CTN_IOPRE";
    case SkolemId::SK_FIRST_CTN_IOPOST: return "SK_FIRST_CTN_IOPOST";
    case SkolemId::SK_FIRST_CTN_RFCPRE: return "SK_FIRST_CTN_RFCPRE";
    case SkolemId::SK_FIRST_CTN_RFCPOST: return "SK_FIRST_CTN_RFCPOST";
    case SkolemId::SK_PREFIX: return "SK_PREFIX";
    case SkolemId::SK_SUFFIX_REM: return "SK_SUFFIX_REM";
    case SkolemId::SK_NUM_OCCUR: return "SK_NUM_OCCUR";
    case SkolemId::SK_OCCUR_INDEX: return "SK_OCCUR_INDEX";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, SkolemId id)
{
  out << toString(id);
  return out;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
