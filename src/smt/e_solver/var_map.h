/*********************                                                        */
/*! \file var_map.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Mapping of variables between two NodeManagers
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__E_SOLVER__VAR_MAP_H
#define CVC4__SMT__E_SOLVER__VAR_MAP_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"

namespace CVC4 {
namespace smt {

class VarMap
{
 public:
  VarMap(NodeManager* nm1, NodeManager* nm2) : d_nm1(nm1), d_nm2(nm2) {}
  ~VarMap()
  {
    {
      NodeManagerScope nms(d_nm1);
      for (std::pair<const TypeNode, TypeNode>& kv : d_revTypeMap)
      {
        d_revTypeMap[kv.first] = TypeNode::null();
      }
    }
    {
      NodeManagerScope nms(d_nm2);
      for (std::pair<const TypeNode, TypeNode>& kv : d_typeMap)
      {
        d_typeMap[kv.first] = TypeNode::null();
      }
    }
    {
      NodeManagerScope nms(d_nm1);
      d_map.clear();
      d_typeMap.clear();
      d_keepAliveFrom.clear();
    }
    {
      NodeManagerScope nms(d_nm2);
      d_revMap.clear();
      d_revTypeMap.clear();
      d_keepAliveTo.clear();
    }
  }

  Node importNode(TNode n)
  {
    return exportNodeInternal(d_nm1,
                              d_nm2,
                              n,
                              d_map,
                              d_revMap,
                              d_typeMap,
                              d_revTypeMap,
                              d_keepAliveTo);
  }

  Node exportNode(TNode n)
  {
    return exportNodeInternal(d_nm2,
                              d_nm1,
                              n,
                              d_revMap,
                              d_map,
                              d_revTypeMap,
                              d_typeMap,
                              d_keepAliveFrom);
  }

  Node exportNodeInternal(
      NodeManager* from,
      NodeManager* to,
      TNode n,
      std::unordered_map<TNode, TNode, TNodeHashFunction>& nodeMap,
      std::unordered_map<TNode, TNode, TNodeHashFunction>& revNodeMap,
      std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>& typeNodeMap,
      std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>&
          revTypeNodeMap,
      std::vector<Node>& keepAlive)
  {
    NodeManagerScope nmsTo(to);
    std::unordered_map<TNode, Node, TNodeHashFunction> result;
    std::vector<TNode> toVisit{n};

    while (!toVisit.empty())
    {
      TNode curr = toVisit.back();
      toVisit.pop_back();

      if (result.find(curr) != result.end())
      {
        if (!result[curr].isNull())
        {
          continue;
        }

        if (nodeMap.find(curr) != nodeMap.end())
        {
          result[curr] = nodeMap[curr];
        }
        else if (curr.getNumChildren() == 0)
        {
          if (curr.getKind() == kind::SKOLEM
              || curr.getKind() == kind::VARIABLE)
          {
            TypeNode tn;
            TypeNode ctn;
            {
              NodeManagerScope nmsFrom(from);
              ctn = curr.getType();
            }
            {
              NodeManagerScope nmsFrom(to);
              tn = exportTypeNode(from, to, ctn, typeNodeMap, revTypeNodeMap);
            }
            std::stringstream ss;
            {
              NodeManagerScope nmsFrom(from);
              ss << "_" << curr;
            }
            Node sk = to->mkSkolem(ss.str(), tn);
            result[curr] = sk;
            nodeMap[curr] = sk;
            revNodeMap[sk] = curr;

            keepAlive.emplace_back(sk);
          }
          else if (curr.getKind() == kind::BOOLEAN_TERM_VARIABLE)
          {
            Node sk = to->mkBooleanTermVariable();
            result[curr] = sk;
            nodeMap[curr] = sk;
            revNodeMap[sk] = curr;

            keepAlive.emplace_back(sk);
          }
          else if (curr.getKind() == kind::BOUND_VARIABLE)
          {
            TypeNode tn;
            TypeNode ctn;
            {
              NodeManagerScope nmsFrom(from);
              ctn = curr.getType();
            }
            {
              NodeManagerScope nmsFrom(to);
              tn = exportTypeNode(from, to, ctn, typeNodeMap, revTypeNodeMap);
            }
            std::stringstream ss;
            {
              NodeManagerScope nmsFrom(from);
              ss << "_" << curr;
            }
            Node sk = to->mkBoundVar(ss.str(), tn);
            result[curr] = sk;
            nodeMap[curr] = sk;
            revNodeMap[sk] = curr;

            keepAlive.emplace_back(sk);
          }
          else if (curr.isConst())
          {
            switch (curr.getKind())
            {
              case kind::UNINTERPRETED_CONSTANT:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::UninterpretedConstant>());
                break;
              case kind::ABSTRACT_VALUE:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::AbstractValue>());
                break;
              case kind::BUILTIN:
                result[curr] = to->mkConst(curr.getConst<::CVC4::Kind>());
                break;
              case kind::TYPE_CONSTANT:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::TypeConstant>());
                break;
              case kind::CONST_BOOLEAN:
                result[curr] = to->mkConst(curr.getConst<bool>());
                break;
              case kind::DIVISIBLE_OP:
                result[curr] = to->mkConst(curr.getConst<::CVC4::Divisible>());
                break;
              case kind::CONST_RATIONAL:
                result[curr] = to->mkConst(curr.getConst<::CVC4::Rational>());
                break;
              case kind::IAND_OP:
                result[curr] = to->mkConst(curr.getConst<::CVC4::IntAnd>());
                break;
              case kind::BITVECTOR_TYPE:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorSize>());
                break;
              case kind::CONST_BITVECTOR:
                result[curr] = to->mkConst(curr.getConst<::CVC4::BitVector>());
                break;
              case kind::BITVECTOR_BITOF_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorBitOf>());
                break;
              case kind::BITVECTOR_EXTRACT_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorExtract>());
                break;
              case kind::BITVECTOR_REPEAT_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorRepeat>());
                break;
              case kind::BITVECTOR_ROTATE_LEFT_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorRotateLeft>());
                break;
              case kind::BITVECTOR_ROTATE_RIGHT_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorRotateRight>());
                break;
              case kind::BITVECTOR_SIGN_EXTEND_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorSignExtend>());
                break;
              case kind::BITVECTOR_ZERO_EXTEND_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::BitVectorZeroExtend>());
                break;
              case kind::INT_TO_BITVECTOR_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::IntToBitVector>());
                break;
              case kind::CONST_FLOATINGPOINT:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::FloatingPoint>());
                break;
              case kind::CONST_ROUNDINGMODE:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::RoundingMode>());
                break;
              case kind::FLOATINGPOINT_TYPE:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::FloatingPointSize>());
                break;
              case kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR_OP:
                result[curr] = to->mkConst(
                    curr.getConst<::CVC4::FloatingPointToFPIEEEBitVector>());
                break;
              case kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT_OP:
                result[curr] = to->mkConst(
                    curr.getConst<::CVC4::FloatingPointToFPFloatingPoint>());
                break;
              case kind::FLOATINGPOINT_TO_FP_REAL_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::FloatingPointToFPReal>());
                break;
              case kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR_OP:
                result[curr] = to->mkConst(
                    curr.getConst<::CVC4::FloatingPointToFPSignedBitVector>());
                break;
              case kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR_OP:
                result[curr] =
                    to->mkConst(curr.getConst<
                                ::CVC4::FloatingPointToFPUnsignedBitVector>());
                break;
              case kind::FLOATINGPOINT_TO_FP_GENERIC_OP:
                result[curr] = to->mkConst(
                    curr.getConst<::CVC4::FloatingPointToFPGeneric>());
                break;
              case kind::FLOATINGPOINT_TO_UBV_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::FloatingPointToUBV>());
                break;
              case kind::FLOATINGPOINT_TO_UBV_TOTAL_OP:
                result[curr] = to->mkConst(
                    curr.getConst<::CVC4::FloatingPointToUBVTotal>());
                break;
              case kind::FLOATINGPOINT_TO_SBV_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::FloatingPointToSBV>());
                break;
              case kind::FLOATINGPOINT_TO_SBV_TOTAL_OP:
                result[curr] = to->mkConst(
                    curr.getConst<::CVC4::FloatingPointToSBVTotal>());
                break;
              case kind::STORE_ALL:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::ArrayStoreAll>());
                break;
              case kind::DATATYPE_TYPE:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::DatatypeIndexConstant>());
                break;
              case kind::ASCRIPTION_TYPE:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::AscriptionType>());
                break;
              case kind::TUPLE_UPDATE_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::TupleUpdate>());
                break;
              case kind::RECORD_UPDATE_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::RecordUpdate>());
                break;
              case kind::EMPTYSET:
                result[curr] = to->mkConst(curr.getConst<::CVC4::EmptySet>());
                break;
              case kind::SINGLETON_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::SingletonOp>());
                break;
              case kind::EMPTYBAG:
                result[curr] = to->mkConst(curr.getConst<::CVC4::EmptyBag>());
                break;
              case kind::MK_BAG_OP:
                result[curr] = to->mkConst(curr.getConst<::CVC4::MakeBagOp>());
                break;
              case kind::CONST_STRING:
                result[curr] = to->mkConst(curr.getConst<::CVC4::String>());
                break;
              case kind::CONST_SEQUENCE:
                result[curr] = to->mkConst(curr.getConst<::CVC4::Sequence>());
                break;
              case kind::REGEXP_REPEAT_OP:
                result[curr] =
                    to->mkConst(curr.getConst<::CVC4::RegExpRepeat>());
                break;
              case kind::REGEXP_LOOP_OP:
                result[curr] = to->mkConst(curr.getConst<::CVC4::RegExpLoop>());
                break;

              default: Unhandled() << "not implemented: " << curr.getKind();
            }
          }
        }
        else
        {
          NodeManagerScope nms(to);
          NodeBuilder<> nb(curr.getKind());
          if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            nb << result[curr.getOperator()];
          }
          for (const TNode& currc : curr)
          {
            nb << result[currc];
          }
          result[curr] = nb;
        }

        continue;
      }

      {
        NodeManagerScope nms(to);
        result[curr] = Node::null();
      }
      toVisit.emplace_back(curr);
      if (curr.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        // XXX: This is a very ugly hack to get the operator as a TNode
        toVisit.emplace_back(curr[-1]);  //.getOperator());
      }
      toVisit.insert(toVisit.end(), curr.begin(), curr.end());
    }

    return result[n];
  }

  TypeNode exportTypeNode(
      NodeManager* from,
      NodeManager* to,
      TypeNode tn,
      std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>& typeNodeMap,
      std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>&
          revTypeNodeMap)
  {
    if (theory::kindToTheoryId(tn.getKind()) == theory::THEORY_DATATYPES)
    {
      Unimplemented() << "Cannot export datatypes";
    }
    if (tn.getMetaKind() == kind::metakind::PARAMETERIZED
        && tn.getKind() != kind::SORT_TYPE)
    {
      Unimplemented() << "Cannot export parametrized types";
    }
    if (tn.getKind() == kind::TYPE_CONSTANT)
    {
      return to->mkTypeConst(tn.getConst<TypeConstant>());
    }
    else if (tn.getKind() == kind::BITVECTOR_TYPE)
    {
      return to->mkBitVectorType(tn.getConst<BitVectorSize>());
    }
    else if (tn.getKind() == kind::FLOATINGPOINT_TYPE)
    {
      return to->mkFloatingPointType(tn.getConst<FloatingPointSize>());
    }
    else if (tn.getKind() == kind::FLOATINGPOINT_TYPE)
    {
      return to->mkFloatingPointType(tn.getConst<FloatingPointSize>());
    }
    else if (tn.getKind() == kind::FUNCTION_TYPE)
    {
      TypeNode range = exportTypeNode(
          from, to, tn.getRangeType(), typeNodeMap, revTypeNodeMap);
      std::vector<TypeNode> args;
      for (const TypeNode& tnn : tn.getArgTypes())
      {
        args.emplace_back(
            exportTypeNode(from, to, tnn, typeNodeMap, revTypeNodeMap));
      }
      NodeManagerScope nms(to);
      TypeNode res = to->mkFunctionType(args, range);
      return res;
    }
    else if (tn.getNumChildren() == 0)
    {
      if (tn.getKind() == kind::SORT_TYPE)
      {
        if (typeNodeMap.find(tn) == typeNodeMap.end())
        {
          std::stringstream ss;
          {
            NodeManagerScope nms(from);
            ss << "_";
            ss << tn;
          }
          NodeManagerScope nms(to);
          TypeNode sort = to->mkSort(ss.str());
          typeNodeMap[tn] = sort;
          revTypeNodeMap[sort] = tn;
        }
        return typeNodeMap[tn];
      }
      Unimplemented() << "Cannot export 0-arity " << tn;
    }
    Unimplemented() << "Cannot export " << tn;
  }

 private:
  NodeManager* d_nm1;
  NodeManager* d_nm2;
  std::unordered_map<TNode, TNode, TNodeHashFunction> d_map;
  std::unordered_map<TNode, TNode, TNodeHashFunction> d_revMap;
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction> d_typeMap;
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction> d_revTypeMap;
  std::vector<Node> d_keepAliveTo;
  std::vector<Node> d_keepAliveFrom;
};

}  // namespace smt
}  // namespace CVC4

#endif
