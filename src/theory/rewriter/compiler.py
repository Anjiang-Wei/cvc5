#!/usr/bin/env python3

import argparse
import re
import sys

from subprocess import Popen, PIPE, STDOUT
from ir import Assign, Assert, optimize_ir
from node import *
from rule import Rule
from parser import parse_rules

from backend_lfsc import collect_params

op_to_kind = {
    Op.BVUGT: 'BITVECTOR_UGT',
    Op.BVUGE: 'BITVECTOR_UGE',
    Op.BVSGT: 'BITVECTOR_SGT',
    Op.BVSGE: 'BITVECTOR_SGE',
    Op.BVSLT: 'BITVECTOR_SLT',
    Op.BVSLE: 'BITVECTOR_SLE',
    Op.BVULT: 'BITVECTOR_ULT',
    Op.BVULE: 'BITVECTOR_ULE',
    Op.BVNEG: 'BITVECTOR_NEG',
    Op.BVADD: 'BITVECTOR_PLUS',
    Op.BVSUB: 'BITVECTOR_SUB',
    Op.CONCAT: 'BITVECTOR_CONCAT',
    Op.ZERO_EXTEND: 'BITVECTOR_ZERO_EXTEND',
    Op.NOT: 'NOT',
    Op.EQ: 'EQUAL',
}

op_to_lfsc = {
    Op.BVUGT: 'bvugt',
    Op.BVUGE: 'bvuge',
    Op.BVSGT: 'bvsgt',
    Op.BVSGE: 'bvsge',
    Op.BVSLT: 'bvslt',
    Op.BVSLE: 'bvsle',
    Op.BVULT: 'bvult',
    Op.BVULE: 'bvule',
    Op.BVNEG: 'bvneg',
    Op.BVADD: 'bvadd',
    Op.BVSUB: 'bvsub',
    Op.CONCAT: 'concat',
    Op.ZERO_EXTEND: 'zero_extend',
    Op.NOT: 'not',
    Op.EQ: '=',
}


op_to_nindex = {
    Op.BVUGT: 0,
    Op.BVUGE: 0,
    Op.BVSGT: 0,
    Op.BVSGE: 0,
    Op.BVSLT: 0,
    Op.BVSLE: 0,
    Op.BVULT: 0,
    Op.BVULE: 0,
    Op.BVNEG: 0,
    Op.BVADD: 0,
    Op.BVSUB: 0,
    Op.CONCAT: 0,
    Op.ZERO_EXTEND: 1,
    Op.NOT: 0,
    Op.EQ: 0,
}


def rule_to_in_ir(rvars, lhs):
    def expr_to_ir(expr, path, vars_seen, out_ir, in_index = False):
        if isinstance(expr, Fn):
            out_ir.append(
                Assert(
                    Fn(Op.EQ,
                       [Fn(Op.GET_KIND, [GetChild(path)]),
                        KindConst(expr.op)])))
            for i, child in enumerate(expr.children):
                index = i if i < op_to_nindex[expr.op] else i - op_to_nindex[expr.op]
                expr_to_ir(child, path + [index], vars_seen, out_ir, i < op_to_nindex[expr.op])

            if isinstance(expr.op, Fn):
                pass

        elif isinstance(expr, Var):
            if expr.name in vars_seen:
                out_ir.append(
                    Assert(Fn(Op.EQ,
                              [Var(expr.name), GetChild(path)])))
            else:
                if in_index:
                    index_expr = GetIndex(path)
                    index_expr.sort = Sort(BaseSort.Int, [])
                    out_ir.append(Assign(expr.name, index_expr))
                else:
                    out_ir.append(Assign(expr.name, GetChild(path)))

                if expr.sort is not None and expr.sort.base == BaseSort.BitVec:
                    width = expr.sort.children[0]
                    if isinstance(width, Var) and not width.name in vars_seen:
                        bv_size_expr = Fn(Op.BV_SIZE, [GetChild(path)])
                        bv_size_expr.sort = Sort(BaseSort.Int, [])
                        out_ir.append(Assign(width.name, bv_size_expr))
                        vars_seen.add(width.name)

                vars_seen.add(expr.name)
        elif isinstance(expr, BVConst):
            if isinstance(expr.bw, Var) and not expr.bw.name in vars_seen:
                bv_size_expr = Fn(Op.BV_SIZE, [GetChild(path)])
                bv_size_expr.sort = Sort(BaseSort.Int, [])
                out_ir.append(Assign(expr.bw.name, bv_size_expr))
                vars_seen.add(expr.bw.name)

            out_ir.append(
                Assert(Fn(
                    Op.EQ,
                    [GetChild(path), Fn(Op.MK_CONST, [expr])])))
        elif isinstance(expr, IntConst):
            out_ir.append(
                Assert(
                    Fn(Op.EQ,
                       [Fn(Op.GET_KIND, [GetChild(path)]),
                        KindConst(expr.op)])))

    out_ir = []
    vars_seen = set()

    expr_to_ir(lhs, [], vars_seen, out_ir)
    return out_ir


def rule_to_out_expr(expr):
    if isinstance(expr, Fn):
        new_children = [rule_to_out_expr(child) for child in expr.children]
        return Fn(Op.MK_NODE, [KindConst(expr.op)] + new_children)
    elif isinstance(expr, BoolConst) or isinstance(expr, BVConst):
        return Fn(Op.MK_CONST, [expr])
    else:
        return expr


def expr_to_code(expr):
    if isinstance(expr, Fn):
        args = [expr_to_code(child) for child in expr.children]
        if expr.op == Op.EQ:
            return '({} == {})'.format(args[0], args[1])
        elif expr.op == Op.GET_KIND:
            return '{}.getKind()'.format(args[0])
        elif expr.op == Op.BV_SIZE:
            return 'bv::utils::getSize({})'.format(args[0])
        elif expr.op == Op.MK_CONST:
            return 'nm->mkConst({})'.format(', '.join(args))
        elif expr.op == Op.MK_NODE:
            return 'nm->mkNode({})'.format(', '.join(args))
    elif isinstance(expr, GetChild):
        path_str = ''.join(['[{}]'.format(i) for i in expr.path])
        return '__node{}'.format(path_str)
    elif isinstance(expr, GetIndex):
        path_str = ''.join(['[{}]'.format(i) for i in expr.path[:-1]])
        return 'bv::utils::getIndex(__node{}, {})'.format(path_str, expr.path[-1])
    elif isinstance(expr, BoolConst):
        return ('true' if expr.val else 'false')
    elif isinstance(expr, BVConst):
        bw_code = expr_to_code(expr.bw)
        return 'BitVector({}, Integer({}))'.format(bw_code, expr.val)
    elif isinstance(expr, KindConst):
        return 'kind::{}'.format(op_to_kind[expr.val])
    elif isinstance(expr, Var):
        return expr.name


def sort_to_code(sort):
    return 'uint32_t' if sort and sort.base == BaseSort.Int else 'Node'


def ir_to_code(match_instrs):
    code = []
    for instr in match_instrs:
        if isinstance(instr, Assign):
            code.append('{} {} = {};'.format(sort_to_code(instr.expr.sort),
                                             instr.name,
                                             expr_to_code(instr.expr)))
        elif isinstance(instr, Assert):
            code.append(
                'if (!({})) return RewriteResponse(REWRITE_DONE, __node, RewriteRule::NONE);'
                .format(expr_to_code(instr.expr)))

    return '\n'.join(code)


def name_to_enum(name):
    name = re.sub(r'(?<!^)(?=[A-Z])', '_', name).upper()
    return name


def gen_rule(rule):
    out_var = '__ret'
    rule_pattern = """
    RewriteResponse {}(TNode __node) {{
      NodeManager* nm = NodeManager::currentNM();
      {}
      return RewriteResponse(REWRITE_AGAIN, {}, RewriteRule::{});
    }}"""

    in_ir = rule_to_in_ir(rule.rvars, rule.lhs)
    out_ir = [Assign(out_var, rule_to_out_expr(rule.rhs))]
    ir = in_ir + [rule.cond] + out_ir
    opt_ir = optimize_ir(out_var, ir)
    body = ir_to_code(opt_ir)
    return rule_pattern.format(rule.name, body, out_var,
                               name_to_enum(rule.name))


def gen_rule_printer(rule):
    rule_printer_pattern = """
    if (step->d_tag == RewriteRule::{})
    {{
      os << "({} {} _ _ ";
      printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
      os << ")";
      return;
    }}
    """

    # TODO: put in ProofRule instead of recomputing
    params = collect_params(rule)
    params_str = ' '.join(['_'] * len(params))

    return rule_printer_pattern.format(name_to_enum(rule.name), name_to_enum(rule.name).lower(), params_str)


def gen_proof_printer(rules):
    printer_pattern = """
    #ifndef CVC4__THEORY__RULES_PRINTER_H
    #define CVC4__THEORY__RULES_PRINTER_H

    #include "proof/rewrite_proof.h"

    namespace CVC4 {{
    namespace theory {{
    namespace rules {{

    class RewriteProofPrinter {{
    public:
    static void printRewriteProof(bool useCache,
                           TheoryProofEngine* tp,
                           const RewriteStep* step,
                           std::ostream& os,
                           ProofLetMap& globalLetMap)
    {{
      if (step->d_tag == RewriteRule::NONE && step->d_children.size() == 0)
      {{
        TypeNode tn = step->d_original.getType();
        if (tn.isBoolean())
        {{
          os << "(iff_symm ";
          tp->printTheoryTerm(step->d_original.toExpr(), os, globalLetMap);
          os << ")";
          return;
        }}
        else
        {{
          os << "(refl _ ";
          tp->printTheoryTerm(step->d_original.toExpr(), os, globalLetMap);
          os << ")";
          return;
        }}
      }}
      else if (step->d_tag == RewriteRule::NONE)
      {{
        switch (step->d_original.getKind()) 
        {{
          case kind::NOT:
          {{
            os << "(symm_formula_op1 not _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << ")";
            return;
          }}

          case kind::BITVECTOR_NEG:
          {{
            os << "(symm_formula_op1 bvneg _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << ")";
            return;
          }}

          case kind::BITVECTOR_ULT:
          {{
            os << "(symm_bvpred bvult _ _ _ _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << " ";
            printRewriteProof(useCache, tp, step->d_children[1], os, globalLetMap);
            os << ")";
            return;
          }}

          case kind::IMPLIES:
          {{
            os << "(symm_formula_op2 impl _ _ _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << " ";
            printRewriteProof(useCache, tp, step->d_children[1], os, globalLetMap);
            os << ")";
            return;
          }}

          case kind::AND:
          {{
            os << "(symm_formula_op2 and _ _ _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << " ";
            printRewriteProof(useCache, tp, step->d_children[1], os, globalLetMap);
            os << ")";
            return;
          }}

          case kind::OR:
          {{
            os << "(symm_formula_op2 or _ _ _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << " ";
            printRewriteProof(useCache, tp, step->d_children[1], os, globalLetMap);
            os << ")";
            return;
          }}

          case kind::EQUAL:
          {{
            os << "(symm_equal _ _ _ _ _ ";
            printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
            os << " ";
            printRewriteProof(useCache, tp, step->d_children[1], os, globalLetMap);
            os << ")";
            return;
          }}

          default: Unimplemented() << "Not supported: " << step->d_original.getKind();
        }}
      }}
      else if (step->d_tag == RewriteRule::UNKNOWN)
      {{
        TypeNode tn = step->d_original.getType();
        if (tn.isBoolean())
        {{
          os << "(trusted_formula_rewrite _ _ ";
          printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
          os << " ";
          tp->printTheoryTerm(step->d_rewritten.toExpr(), os, globalLetMap);
          os << ")";
          return;
        }}
        else
        {{
          os << "(trusted_term_rewrite _ _ _ ";
          printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
          os << " ";
          tp->printTheoryTerm(step->d_rewritten.toExpr(), os, globalLetMap);
          os << ")";
          return;
        }}
      }}
      else if (step->d_tag == RewriteRule::CONST_EVAL)
      {{
        if (step->d_rewritten.getType().isBoolean())
        {{
          os << "(const_eval_f _ _ ";
          printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
          os << " ";
          tp->printTheoryTerm(step->d_rewritten.toExpr(), os, globalLetMap);
          os << ")";
          return;
        }}
        Unreachable();
      }}
      {}
    }}

    static void printProof(TheoryProofEngine *tp, const RewriteProof &rp, std::ostream &os,
                ProofLetMap &globalLetMap) {{
      std::ostringstream paren;
      rp.printCachedProofs(tp, os, paren, globalLetMap);
      os << std::endl;
      printRewriteProof(true, tp, rp.getRewrite(), os, globalLetMap);
      os << paren.str();
    }}

    }};

    }}
    }}
    }}

    #endif
    """
    return format_cpp(printer_pattern.format('\n'.join(gen_rule_printer(rule) for rule in rules)))


def gen_enum(rules):
    enum_pattern = """
    #ifndef CVC4__THEORY__REWRITER_RULES_H
    #define CVC4__THEORY__REWRITER_RULES_H

    namespace CVC4 {{
    namespace theory {{
    namespace rules {{

    enum class RewriteRule {{
      {},
      UNKNOWN,
      CONST_EVAL,
      NONE
    }};

    }}
    }}
    }}

    #endif"""

    return format_cpp(
        enum_pattern.format(','.join(
            name_to_enum(rule.name) for rule in rules)))


def gen_rules_implementation(rules):
    file_pattern = """
    #include "expr/node.h"
    #include "theory/bv/theory_bv_utils.h"
    #include "theory/rewrite_response.h"
    #include "util/bitvector.h"

    namespace CVC4 {{
    namespace theory {{
    namespace rules {{

    {}

    }}
    }}
    }}"""

    rules_code = []
    for rule in rules:
        rules_code.append(gen_rule(rule))

    return format_cpp(file_pattern.format('\n'.join(rules_code)))


def format_cpp(s):
    p = Popen(['clang-format'], stdout=PIPE, stdin=PIPE, stderr=STDOUT)
    out = p.communicate(input=s.encode())[0]
    return out.decode()


def sort_to_lfsc(sort):
    if sort and sort.base == BaseSort.Bool:
        return 'formula'
    else: # if sort.base == BaseSort.BitVec:
        return '(term (BitVec n))'

def expr_to_lfsc(expr):
    if isinstance(expr, Fn):
        if expr.op in [Op.ZERO_EXTEND]:
            args = [expr_to_lfsc(arg) for arg in expr.children]
            return '({} zebv {} _ {})'.format(op_to_lfsc[expr.op], ' '.join(args[:op_to_nindex[expr.op]]), ' '.join(args[op_to_nindex[expr.op]:]))
        else:
            args = [expr_to_lfsc(arg) for arg in expr.children]
            return '({} _ {})'.format(op_to_lfsc[expr.op], ' '.join(args))

    elif isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, BVConst):
        return '(a_bv _ {})'.format('bv{}_{}'.format(expr.val, expr.bw))
    elif isinstance(expr, BoolConst):
        return ('true' if expr.val else 'false')

def rule_to_lfsc(rule):
    rule_pattern = """
    (declare {}
    {}
      (! u (th_holds {})
        (th_holds {}))){}"""
    closing_parens = ''

    rule_name = name_to_enum(rule.name).lower()

    params = collect_params(rule)

    varargs = []

    for param in params:
        sort_str = ''
        if param.sort.base == BaseSort.Int:
            sort_str = 'mpz'
        elif param.sort.base == BaseSort.BitVec:
            sort_str = 'bv'
        else:
            print('Unsupported sort: {}'.format(param.sort_base))
            assert False
        varargs.append('(! {} {}'.format(param.name, sort_str))
        closing_parens += ')'

    varargs.append('(! original {}'.format(sort_to_lfsc(rule.lhs.sort)))
    closing_parens += ')'

    for name, sort in rule.rvars.items():
        varargs.append('(! {} {}'.format(name, sort_to_lfsc(sort)))
        closing_parens += ')'

    if rule.lhs.sort.base == BaseSort.Bool:
        lhs = '(iff original {})'.format(expr_to_lfsc(rule.lhs))
        rhs = '(iff original {})'.format(expr_to_lfsc(rule.rhs))
    else:
        lhs = '(= _ original {})'.format(expr_to_lfsc(rule.lhs))
        rhs = '(= _ original {})'.format(expr_to_lfsc(rule.rhs))

    print(rule_pattern.format(rule_name, '\n'.join(varargs), lhs, rhs, closing_parens))


def type_check(rules):
    for rule in rules:
        infer_types(rule.rvars, rule.lhs)

        # Ensure that we were able to compute the types for the whole left-hand side
        assert rule.lhs.sort is not None


def main():
    # (define-rule SgtEliminate ((x (_ BitVec n)) (y (_ BitVec n))) (bvsgt x y) (bvsgt y x))

    # sgt_eliminate = Rule('SgtEliminate',
    #         {'x': Sort(BaseSort.BitVec, [Var('n', int_sort)]),
    #         'y': Sort(BaseSort.BitVec, [Var('n', int_sort)])},
    #                      BoolConst(True),
    #                      Fn(Op.BVSGT, [Var('x'), Var('y')]),
    #                      Fn(Op.BVSLT, [Var('y'), Var('x')]))

    parser = argparse.ArgumentParser(description='Compile rewrite rules.')
    parser.add_argument('infile',
                        type=argparse.FileType('r'),
                        help='Rule file')
    parser.add_argument('rulesfile',
                        type=argparse.FileType('w'),
                        help='File that lists the rules')
    parser.add_argument('implementationfile',
                        type=argparse.FileType('w'),
                        help='File that implements the rules')
    parser.add_argument('printerfile',
                        type=argparse.FileType('w'),
                        help='File that prints the rule applications')
    parser.add_argument('proofrulesfile',
                        type=argparse.FileType('w'),
                        help='File with the proof rules')

    args = parser.parse_args()

    rules = parse_rules(args.infile.read())

    type_check(rules)

    args.rulesfile.write(gen_enum(rules))
    args.implementationfile.write(gen_rules_implementation(rules))
    args.printerfile.write(gen_proof_printer(rules))

    for rule in rules:
        rule_to_lfsc(rule)


if __name__ == "__main__":
    main()
