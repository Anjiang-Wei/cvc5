#!/usr/bin/env python3

import argparse
import re
import sys

from subprocess import Popen, PIPE, STDOUT
from ir import Assign, Assert, optimize_ir
from node import *
from rule import Rule
from parser import parse_rules

op_to_kind = {
    Op.BVSGT: 'BITVECTOR_SGT',
    Op.BVSLT: 'BITVECTOR_SLT',
    Op.BVULT: 'BITVECTOR_ULT',
    Op.BVULE: 'BITVECTOR_ULE',
    Op.BVNEG: 'BITVECTOR_NEG',
    Op.ZERO_EXTEND: 'BITVECTOR_ZERO_EXTEND',
    Op.NOT: 'NOT',
    Op.EQ: 'EQUAL',
}


def rule_to_in_ir(rvars, lhs):
    def expr_to_ir(expr, path, vars_seen, out_ir):
        if isinstance(expr, Fn):
            out_ir.append(
                Assert(
                    Fn(Op.EQ,
                       [Fn(Op.GET_KIND, [GetChild(path)]),
                        KindConst(expr.op)])))
            for i, child in enumerate(expr.children):
                expr_to_ir(child, path + [i], vars_seen, out_ir)

            if isinstance(expr.op, Fn):
                pass

        elif isinstance(expr, Var):
            if expr.name in vars_seen:
                out_ir.append(
                    Assert(Fn(Op.EQ,
                              [Var(expr.name), GetChild(path)])))
            else:
                out_ir.append(Assign(expr.name, GetChild(path)))

                if expr.sort is not None and expr.sort.base == BaseSort.BitVec:
                    width = expr.sort.args[0]
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

    infer_types(rule.rvars, rule.lhs)
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
      os << "({} ";
      printRewriteProof(useCache, tp, step->d_children[0], os, globalLetMap);
      os << ")";
      return;
    }}
    """
    return rule_printer_pattern.format(name_to_enum(rule.name), rule.name)


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
        switch (step->d_original.getKind())
        {{
          case kind::EQUAL:
          {{
            os << "(iff_symm ";
            tp->printTheoryTerm(step->d_original.toExpr(), os, globalLetMap);
            os << ")";
            return;
          }}

          default:
          {{
            os << "(refl _ ";
            tp->printTheoryTerm(step->d_original.toExpr(), os, globalLetMap);
            os << ")";
            return;
          }}
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

          default: Unimplemented();
        }}
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

    args.rulesfile.write(gen_enum(rules))
    args.implementationfile.write(gen_rules_implementation(rules))
    args.printerfile.write(gen_proof_printer(rules))

    # zero_extend_eliminate = Rule('ZeroExtendEliminate',
    #                      [Var('x', Sort(BaseSort.BitVec, [Var('n', int_sort)]))],
    #                      BoolConst(True),
    #                      Fn(Fn(Op.ZERO_EXTEND, [IntConst(0)]), [Var('x')]),
    #                      Var('x'))
    # print(format_cpp(gen_rule(zero_extend_eliminate)))


if __name__ == "__main__":
    main()
