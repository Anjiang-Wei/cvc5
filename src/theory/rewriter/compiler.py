#!/usr/bin/env python3

import argparse
import re
import sys

from subprocess import Popen, PIPE, STDOUT
from ir import *
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
    Op.BVREDAND: 'BITVECTOR_REDAND',
    Op.BVREDOR: 'BITVECTOR_REDOR',
    Op.BVNEG: 'BITVECTOR_NEG',
    Op.BVADD: 'BITVECTOR_PLUS',
    Op.BVSUB: 'BITVECTOR_SUB',
    Op.BVMUL: 'BITVECTOR_MULT',
    Op.BVSDIV: 'BITVECTOR_SDIV',
    Op.BVUDIV: 'BITVECTOR_UDIV_TOTAL',
    Op.BVSREM: 'BITVECTOR_SREM',
    Op.BVUREM: 'BITVECTOR_UREM_TOTAL',
    Op.BVSMOD: 'BITVECTOR_SMOD',
    Op.BVSHL: 'BITVECTOR_SHL',
    Op.BVLSHR: 'BITVECTOR_LSHR',
    Op.BVASHR: 'BITVECTOR_ASHR',
    Op.ROTATE_LEFT: 'BITVECTOR_ROTATE_LEFT',
    Op.ROTATE_RIGHT: 'BITVECTOR_ROTATE_RIGHT',
    Op.BVNOT: 'BITVECTOR_NOT',
    Op.BVAND: 'BITVECTOR_AND',
    Op.BVOR: 'BITVECTOR_OR',
    Op.BVXOR: 'BITVECTOR_XOR',
    Op.BVNAND: 'BITVECTOR_NAND',
    Op.BVNOR: 'BITVECTOR_NOR',
    Op.BVXNOR: 'BITVECTOR_XNOR',
    Op.CONCAT: 'BITVECTOR_CONCAT',
    Op.BVITE: 'BITVECTOR_ITE',
    Op.BVCOMP: 'BITVECTOR_COMP',
    Op.BVCONST: 'CONST_BITVECTOR',
    Op.ZERO_EXTEND: 'BITVECTOR_ZERO_EXTEND',
    Op.SIGN_EXTEND: 'BITVECTOR_SIGN_EXTEND',
    Op.EXTRACT: 'BITVECTOR_EXTRACT',
    Op.REPEAT: 'BITVECTOR_REPEAT',
    Op.NOT: 'NOT',
    Op.AND: 'AND',
    Op.XOR: 'XOR',
    Op.EQ: 'EQUAL',
    Op.ITE: 'ITE',
}

op_to_const_eval = {
        Op.BVSHL: lambda args: '({}.leftShift({}))'.format(args[0], args[1]),
    Op.BVNEG: lambda args: '(-{})'.format(args[0]),
    Op.EXTRACT: lambda args: '({2}.extract({0}, {1}))'.format(*args),
    Op.BVNOT: lambda args: '(~{})'.format(args[0]),
    Op.CONCAT: lambda args: '({}.concat({}))'.format(args[0], args[1]),
    Op.PLUS: lambda args: '({} + {})'.format(args[0], args[1]),
    Op.MINUS: lambda args: '({} - {})'.format(args[0], args[1]),
    Op.LT: lambda args: '({} < {})'.format(args[0], args[1]),
    Op.GEQ: lambda args: '({} >= {})'.format(args[0], args[1]),
    Op.NOT: lambda args: '(!{})'.format(args[0]),
    Op.AND: lambda args: '({})'.format(' && '.join(args)) if len(args) > 0 else 'true',
    Op.EQ: lambda args: '({} == {})'.format(args[0], args[1]),
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
    Op.BVREDAND: 0,
    Op.BVREDOR: 0,
    Op.BVNEG: 0,
    Op.BVADD: 0,
    Op.BVSUB: 0,
    Op.BVMUL: 0,
    Op.BVSDIV: 0,
    Op.BVUDIV: 0,
    Op.BVSREM: 0,
    Op.BVUREM: 0,
    Op.BVSMOD: 0,
    Op.BVSHL: 0,
    Op.BVLSHR: 0,
    Op.BVASHR: 0,
    Op.ROTATE_LEFT: 1,
    Op.ROTATE_RIGHT: 1,
    Op.BVNOT: 0,
    Op.BVAND: 0,
    Op.BVOR: 0,
    Op.BVXOR: 0,
    Op.BVNAND: 0,
    Op.BVNOR: 0,
    Op.BVXNOR: 0,
    Op.CONCAT: 0,
    Op.BVITE: 0,
    Op.BVCOMP: 0,
    Op.BVCONST: 2,
    Op.ZERO_EXTEND: 1,
    Op.SIGN_EXTEND: 1,
    Op.EXTRACT: 2,
    Op.REPEAT: 1,
    Op.NOT: 0,
    Op.AND: 0,
    Op.XOR: 0,
    Op.EQ: 0,
    Op.ITE: 0,
}


def mk_simple_block(cfg, next_block, instr):
    instr_block = fresh_name('block')
    if next_block:
        cfg[instr_block] = CFGNode([instr],
                                   [CFGEdge(BoolConst(True), next_block)])
    else:
        cfg[instr_block] = CFGNode([instr], [])
    return instr_block


def rule_to_in_ir(cfg, out_block, node_var, rvars, lhs):
    def expr_to_ir(const_checks,
                   next_block,
                   expr,
                   node,
                   vars_seen,
                   in_loop=False):
        if isinstance(expr, Var):
            if expr.name in vars_seen:
                return mk_simple_block(
                    cfg, next_block, Assert(Fn(Op.EQ, [expr, node]), in_loop))
            else:
                if expr.sort is not None and expr.sort.base == BaseSort.BitVec:
                    width = expr.sort.children[0]
                    if isinstance(width, Var) and not width.name in vars_seen:
                        bv_size_expr = Fn(Op.BV_SIZE, [node])
                        bv_size_expr.sort = Sort(BaseSort.Int, [], True)
                        # TODO: should resolve earlier?
                        width.sort = Sort(BaseSort.Int, [], True)
                        next_block = mk_simple_block(
                            cfg, next_block, Assign(width, bv_size_expr))
                        vars_seen.add(width.name)

                next_block = mk_simple_block(cfg, next_block,
                                             Assign(expr, node))

                return next_block

        elif expr.sort.const:
            if isinstance(expr, Fn) and expr.op == Op.BVCONST:
                # bvval =
                # next_block = mk_simple_block(
                #     cfg, next_block,
                #     Assert(
                #         Fn(Op.EQ,
                #            [Fn(Op.GET_KIND, [node]),
                #             KindConst(expr.op)]), in_loop))

                if isinstance(expr.children[0],
                              Var) and expr.children[0] not in vars_seen:
                    next_block = mk_simple_block(
                        cfg, next_block,
                        Assign(expr.children[0], Fn(Op.BV_SIZE, [node])))

                    next_block = expr_to_ir(const_checks, next_block,
                                            expr.children[0],
                                            Fn(Op.BV_SIZE,
                                               [node]), vars_seen, in_loop)

                if isinstance(expr.children[1],
                              Var) and expr.children[1] not in vars_seen:
                    next_block = expr_to_ir(const_checks, next_block,
                                            expr.children[1],
                                            Fn(Op.BV_SIZE,
                                               [node]), vars_seen, in_loop)

                next_block = mk_simple_block(
                    cfg, next_block,
                    Assert(
                        Fn(Op.EQ,
                           [Fn(Op.GET_KIND, [node]),
                            KindConst(expr.op)]), in_loop))

                return next_block

            # TODO: node.sort should not be None
            instr = None
            if node.sort and node.sort.const:
                instr = Fn(Op.EQ, [node, expr])
            else:
                instr = Fn(Op.EQ, [node, Fn(Op.MK_CONST, [expr])])

            return mk_simple_block(cfg, next_block, Assert(instr, in_loop))

        elif isinstance(expr, Fn):
            if expr.op in commutative_ops and expr.op in associative_ops:
                nlist_children = [
                    child for child in expr.children
                    if child.sort.base != BaseSort.List
                ]
                loop_idxs = [
                    Var(fresh_name('loopi'), Sort(BaseSort.Int, [], True))
                    for _ in nlist_children
                ]

                # Assign the remainder of the list
                if len(nlist_children) != len(expr.children):
                    list_child = next(child for child in expr.children
                                      if child.sort.base == BaseSort.List)
                    print(loop_idxs)
                    cond = Fn(Op.AND, [Fn(Op.NOT, [Fn(Op.EQ, [Var('i', Sort(BaseSort.Int, [], True)), idx])]) for idx in loop_idxs])

                    # TODO: Do at creation-time
                    cond.sort = Sort(BaseSort.Bool, [], True)
                    for child in cond.children:
                        child.sort = Sort(BaseSort.Bool, [], True)
                        child.children[0].sort = Sort(BaseSort.Bool, [], True)

                    next_block = mk_simple_block(
                        cfg, next_block,
                        Assign(list_child,
                               Fn(Op.GET_CHILDREN, [node, cond])))

                for i, child in reversed(list(enumerate(nlist_children))):
                    sub_expr_vars_seen = vars_seen.copy()
                    for child2 in nlist_children[:i]:
                        sub_expr_vars_seen |= collect_vars(child2)

                    loop_idx = loop_idxs[i]
                    loop_var_sort = Sort(child.sort.base, child.sort.children)
                    loop_var = Var(fresh_name('loopv'), loop_var_sort)
                    next_block = expr_to_ir(const_checks, next_block, child,
                                            loop_var, sub_expr_vars_seen, True)
                    next_block = mk_simple_block(
                        cfg, next_block,
                        Assign(loop_var, Fn(Op.GET_CHILD, [node, loop_idx])))

                    for j in range(i):
                        check = Fn(Op.NOT,
                                   [Fn(Op.EQ, [loop_idx, loop_idxs[j]])])
                        # Use infer types
                        check.sort = Sort(BaseSort.Bool, [], True)
                        check.children[0].sort = Sort(BaseSort.Bool, [], True)
                        next_block = mk_simple_block(cfg, next_block,
                                                     Assert(check, True))

                    loop_block = fresh_name('loop')
                    cfg[loop_block] = CFGLoop(loop_idx, node, next_block)
                    next_block = loop_block
            elif expr.op in associative_ops:
                nlist_children = [
                    child for child in expr.children
                    if child.sort.base != BaseSort.List
                ]
                loop_idxs = [
                    (Var(fresh_name('loopi'), Sort(BaseSort.Int, [], True)) if child.sort.base != BaseSort.List else None)
                    for child in expr.children
                ]

                # Assign the list children
                if len(nlist_children) != len(expr.children):
                    for i, child in enumerate(expr.children):
                        if child.sort.base != BaseSort.List:
                            continue

                        var_i = Var('i', Sort(BaseSort.Int, [], True))
                        conds = []
                        if i != 0:
                            conds.append(Fn(Op.LT, [loop_idxs[i - 1], var_i]))
                        if i != len(expr.children) - 1:
                            conds.append(Fn(Op.LT, [var_i, loop_idxs[i + 1]]))
                        cond = Fn(Op.AND, conds)

                        # TODO: Do at creation-time
                        cond.sort = Sort(BaseSort.Bool, [], True)
                        for cond_child in cond.children:
                            cond_child.sort = Sort(BaseSort.Bool, [], True)

                        next_block = mk_simple_block(
                            cfg, next_block,
                            Assign(child,
                                   Fn(Op.GET_CHILDREN, [node, cond])))

                for i, child in reversed(list(enumerate(expr.children))):
                    if child.sort and child.sort.base == BaseSort.List:
                        continue

                    sub_expr_vars_seen = vars_seen.copy()
                    for child2 in expr.children[:i - 1]:
                        sub_expr_vars_seen |= collect_vars(child2)

                    loop_idx = loop_idxs[i]
                    loop_var_sort = Sort(child.sort.base, child.sort.children)
                    loop_var = Var(fresh_name('loopv'), loop_var_sort)
                    next_block = expr_to_ir(const_checks, next_block, child,
                                            loop_var, sub_expr_vars_seen, True)
                    next_block = mk_simple_block(
                        cfg, next_block,
                        Assign(loop_var, Fn(Op.GET_CHILD, [node, loop_idx])))

                    for j in range(i):
                        if not loop_idxs[j]:
                            continue

                        check = Fn(Op.LT, [loop_idxs[j], loop_idx])
                        # Use infer types
                        check.sort = Sort(BaseSort.Bool, [], True)
                        next_block = mk_simple_block(cfg, next_block,
                                                     Assert(check, True))

                    loop_block = fresh_name('loop')
                    cfg[loop_block] = CFGLoop(loop_idx, node, next_block)
                    next_block = loop_block
            else:
                for i, child in reversed(list(enumerate(expr.children))):
                    sub_expr_vars_seen = vars_seen.copy()
                    for child2 in expr.children[:i]:
                        sub_expr_vars_seen |= collect_vars(child2)

                    child_node = None
                    if i < op_to_nindex[expr.op]:
                        child_node = Fn(Op.GET_INDEX, [node, IntConst(i)])
                        child_node.sort = Sort(BaseSort.Int, [], True)
                    else:
                        child_node = Fn(
                            Op.GET_CHILD,
                            [node, IntConst(i - op_to_nindex[expr.op])])
                    next_block = expr_to_ir(const_checks, next_block, child,
                                            child_node, sub_expr_vars_seen,
                                            in_loop)

            return mk_simple_block(
                cfg, next_block,
                Assert(
                    Fn(Op.EQ, [Fn(Op.GET_KIND, [node]),
                               KindConst(expr.op)]), in_loop))

        elif isinstance(expr, BVConst):
            assert False
            next_block = mk_simple_block(
                cfg, next_block,
                Assert(Fn(
                    Op.EQ,
                    [GetChild(path), Fn(Op.MK_CONST, [expr])]), in_loop))

            if isinstance(expr.bw, Var) and not expr.bw.name in vars_seen:
                bv_size_expr = Fn(Op.BV_SIZE, [GetChild(path)])
                bv_size_expr.sort = Sort(BaseSort.Int, [])
                next_block = mk_simple_block(
                    cfg, next_block, Assign(expr.bw.name, bv_size_expr))
                vars_seen.add(expr.bw.name)

            return next_block

        print('Unsupported {}'.format(expr))
        assert False

    vars_seen = set()
    const_check_block = fresh_name('block')
    const_checks = []
    entry = expr_to_ir(const_checks, const_check_block, lhs, node_var,
                       vars_seen)
    cfg[const_check_block] = CFGNode(const_checks,
                                     [CFGEdge(BoolConst(True), out_block)])
    return entry


name_id = 0


def fresh_name(prefix):
    global name_id
    name_id += 1
    return prefix + str(name_id)


def rule_to_out_expr(cfg, next_block, res, expr):
    def expr_to_out_expr(expr):
        if isinstance(expr, Fn):
            new_args = []
            for child in expr.children:
                new_args.append(expr_to_out_expr(child))
            return Fn(Op.MK_NODE, [KindConst(expr.op)] + new_args)
        else:
            return expr

    def rule_to_out_expr_rec(cfg, next_block, res, expr):
        if isinstance(expr, Fn):
            if expr.op == Op.COND:
                edges = []
                for case in expr.children:
                    cond = case.children[0]
                    result = rule_to_out_expr(cfg, next_block, res,
                                              case.children[1])
                    edges.append(CFGEdge(cond, result))
                cond_block = fresh_name('block')
                cfg[cond_block] = CFGNode([], edges)
                return cond_block
            elif expr.op == Op.FAIL:
                return mk_simple_block(cfg, next_block,
                                       Assert(BoolConst(False), False))
            elif expr.op == Op.LET:
                next_block = rule_to_out_expr(cfg, next_block, res,
                                              expr.children[2])
                next_block = rule_to_out_expr(cfg, next_block,
                                              expr.children[0],
                                              expr.children[1])
                return next_block
            elif expr.op == Op.MAP:
                lambda_var = expr.children[0].children[0]
                new_body = expr_to_out_expr(expr.children[0].children[1])
                return mk_simple_block(cfg, next_block, Assign(res, Fn(Op.MAP, [Fn(Op.LAMBDA, [lambda_var, new_body]), expr.children[1]])))
            elif expr.op == Op.BVCONST:
                new_vars = [
                    Var(fresh_name('__v'), child.sort)
                    for child in expr.children
                ]
                bvc = Fn(Op.BVCONST, new_vars)
                bvc.sort = expr.sort
                assign = None
                if res.sort and res.sort.const:
                    assign = Assign(res, bvc)
                else:
                    mk_const = Fn(Op.MK_CONST, [bvc])
                    mk_const.sort = Sort(bvc.sort.base, bvc.sort.children)
                    assign = Assign(res, mk_const)

                assign_block = fresh_name('block')
                if next_block:
                    cfg[assign_block] = CFGNode(
                        [assign], [CFGEdge(BoolConst(True), next_block)])
                else:
                    cfg[assign_block] = CFGNode([assign], [])

                next_block = assign_block
                for var, child in zip(new_vars, expr.children):
                    next_block = rule_to_out_expr(cfg, next_block, var, child)
                return next_block
            else:
                new_vars = [
                    Var(fresh_name('__v'), child.sort)
                    for child in expr.children
                ]

                assign = None
                if expr.sort.const:
                    fn = Fn(expr.op, new_vars)
                    fn.sort = expr.sort
                    if res.sort and res.sort.const:
                        assign = Assign(res, fn)
                    else:
                        mk_const = Fn(Op.MK_CONST, [fn])
                        mk_const.sort = Sort(fn.sort.base, fn.sort.children)
                        assign = Assign(res, mk_const)
                else:
                    # If we have a non-constant expression with constant arguments,
                    # we have to cast the constant arguments to terms
                    new_args = []
                    for i, new_var in enumerate(new_vars):
                        if new_var.sort.const and i >= op_to_nindex[expr.op]:
                            mk_const = Fn(Op.MK_CONST, [new_var])
                            mk_const.sort = Sort(new_var.sort.base, new_var.sort.children)
                            new_args.append(mk_const)
                        else:
                            new_args.append(new_var)

                    assign = Assign(
                        res, Fn(Op.MK_NODE, [KindConst(expr.op)] + new_args))

                assign_block = fresh_name('block')
                if next_block:
                    cfg[assign_block] = CFGNode(
                        [assign], [CFGEdge(BoolConst(True), next_block)])
                else:
                    cfg[assign_block] = CFGNode([assign], [])

                next_block = assign_block
                for var, child in zip(new_vars, expr.children):
                    next_block = rule_to_out_expr(cfg, next_block, var, child)
                return next_block
        elif isinstance(expr, BoolConst):
            assign_block = fresh_name('block')
            res.sort = Sort(BaseSort.Bool, [])
            assign = Assign(res, expr)
            if next_block:
                cfg[assign_block] = CFGNode(
                    [assign], [CFGEdge(BoolConst(True), next_block)])
            else:
                assign.expr = Fn(Op.MK_CONST, [assign.expr])
                cfg[assign_block] = CFGNode([assign], [])
            return assign_block
        elif isinstance(expr, IntConst):
            assign_block = fresh_name('block')
            res.sort = Sort(BaseSort.Int, [], True)
            assign = Assign(res, expr)
            if next_block:
                cfg[assign_block] = CFGNode(
                    [assign], [CFGEdge(BoolConst(True), next_block)])
            else:
                cfg[assign_block] = CFGNode([assign], [])
            return assign_block
        elif isinstance(expr, Var):
            assign_block = fresh_name('block')
            assign = Assign(res, expr)
            res.sort = expr.sort
            if next_block:
                cfg[assign_block] = CFGNode(
                    [assign], [CFGEdge(BoolConst(True), next_block)])
            else:
                cfg[assign_block] = CFGNode([assign], [])
            return assign_block
        else:
            return expr

    return rule_to_out_expr_rec(cfg, next_block, res, expr)


def expr_to_code(expr):
    if isinstance(expr, Fn):
        args = [expr_to_code(child) for child in expr.children]

        if expr.op == Op.EQ:
            return '({} == {})'.format(args[0], args[1])
        elif expr.op == Op.GET_KIND:
            return '{}.getKind()'.format(args[0])
        elif expr.op == Op.BV_SIZE:
            return 'bv::utils::getSize({})'.format(args[0])
        elif expr.op == Op.BVCONST:
            return 'BitVector({}, {})'.format(args[0], args[1])
        elif expr.op == Op.MK_CONST:
            return 'nm->mkConst({})'.format(', '.join(args))
        elif expr.op == Op.MK_NODE:
            kind = expr.children[0].val

            list_arg = None
            for child in expr.children:
                if child.sort and child.sort.base == BaseSort.List:
                    list_arg = child.sort
                    break

            arg_str = None
            if list_arg:
                vec = fresh_name('__vec')
                arg_str = '{}, '.format(args[0])
                arg_str += '[&](){{ std::vector<Node> {0}; {1}; return {0}; }}()'.format(
                    vec, ';'.join(
                        ('{}.push_back({})'.format(vec, arg)
                         if child.sort and child.sort.base != BaseSort.List
                         else '{0}.insert({0}.end(), {1}.begin(), {1}.end())'.
                         format(vec, arg))
                        for arg, child in zip(args[1:], expr.children[1:])))
            elif op_to_nindex[kind] != 0:
                op = 'bv::utils::mkIndexedOp({})'.format(', '.join(
                    args[:op_to_nindex[kind] + 1]))
                arg_str = ', '.join([op] + args[op_to_nindex[kind] + 1:])
            else:
                arg_str = ', '.join(args)

            return 'nm->mkNode({})'.format(arg_str)
        elif expr.op == Op.GET_CHILD:
            return '{}[{}]'.format(args[0], args[1])
        elif expr.op == Op.GET_CHILDREN:
            if len(args) == 1:
                return 'std::vector<Node>({0}.begin(), {0}.end())'.format(args[0])
            else:
                return 'bv::utils::getChildren({}, [&](size_t i) {{ return {}; }})'.format(
                    args[0], args[1])
        elif expr.op == Op.GET_INDEX:
            return 'bv::utils::getIndex({}, {})'.format(args[0], args[1])
        elif expr.sort and expr.sort.const:
            return op_to_const_eval[expr.op](args)
        elif expr.op == Op.MAP:
            return 'bv::utils::mapVector({}, {})'.format(args[1], args[0])
        elif expr.op == Op.LAMBDA:
            return '[&]({} {}) {{ return {}; }}'.format(sort_to_code(expr.children[0].sort), args[0], args[1])
        else:
            print('No code generation for op {} in {}'.format(expr.op, expr))
            assert False
    elif isinstance(expr, BoolConst):
        return ('true' if expr.val else 'false')
    elif isinstance(expr, BVConst):
        bw_code = expr_to_code(expr.bw)
        return 'BitVector({}, Integer({}))'.format(bw_code, expr.val)
    elif isinstance(expr, IntConst):
        return str(expr.val)
    elif isinstance(expr, KindConst):
        return 'kind::{}'.format(op_to_kind[expr.val])
    elif isinstance(expr, Var):
        return expr.name


def sort_to_code(sort):
    if not sort or not sort.const:
        # TODO: null sort should not happen
        if sort.base == BaseSort.List:
            return 'std::vector<{}>'.format(sort_to_code(sort.children[0]))
        else:
            return 'Node'
    elif sort.base == BaseSort.Int:
        return 'uint32_t'
    elif sort.base == BaseSort.BitVec:
        return 'BitVector'


def ir_to_code(match_instrs):
    code = []
    for instr in match_instrs:
        if isinstance(instr, Assign):
            code.append('{} = {};'.format(instr.name,
                                          expr_to_code(instr.expr)))
        elif isinstance(instr, Assert):
            exit = 'continue' if instr.in_loop else 'return RewriteResponse(REWRITE_DONE, __node, RewriteRule::NONE)'
            code.append('if (!({})) {};'.format(expr_to_code(instr.expr),
                                                exit))

    return '\n'.join(code)


def cfg_to_code(block, cfg):
    if isinstance(cfg[block], CFGLoop):
        body = cfg_to_code(cfg[block].body, cfg)
        return """
        for ({} = 0; {} < {}.getNumChildren(); {}++) {{
         {}
        }}""".format(cfg[block].loop_var, cfg[block].loop_var,
                     expr_to_code(cfg[block].domain), cfg[block].loop_var,
                     body)
    else:
        result = ir_to_code(cfg[block].instrs)
        first_edge = True
        for edge in cfg[block].edges:
            branch_code = cfg_to_code(edge.target, cfg)

            if edge.cond == BoolConst(True):
                if first_edge:
                    result += branch_code
                else:
                    result += """
                    else {{
                      {}
                    }}""".format(branch_code)
                break
            else:
                cond_type = 'if' if first_edge else 'else if'

                result += """
                {} ({}) {{
                 {}
                }}""".format(cond_type, expr_to_code(edge.cond), branch_code)

            first_edge = False
        return result


def name_to_enum(name):
    name = re.sub(r'(?<!^)(?=[A-Z])', '_', name).upper()
    return name


def gen_rule(rule):
    node_var = Var('__node', rule.lhs.sort)
    out_var = Var('__ret', Sort(rule.rhs.sort.base, rule.rhs.sort.children))
    rule_pattern = """
    RewriteResponse {}(TNode __node) {{
      NodeManager* nm = NodeManager::currentNM();
      {}
      {}
      return RewriteResponse(REWRITE_AGAIN, {}, RewriteRule::{});
    }}"""

    cfg = {}
    entry = rule_to_out_expr(cfg, None, out_var, rule.rhs)
    match_block = rule_to_in_ir(cfg, entry, node_var, rule.rvars, rule.lhs)

    for name, block in cfg.items():
        print(name)
        print(block)

    optimize_cfg(out_var, match_block, cfg)
    # ir = in_ir + [rule.cond] + out_ir
    # opt_ir = optimize_ir(out_var, ir)

    for name, block in cfg.items():
        print(block)

    cfg_vars = cfg_collect_vars(cfg)
    var_decls = ''
    for var in cfg_vars:
        var_decls += '{} {};\n'.format(sort_to_code(var.sort), var.name)

    body = cfg_to_code(match_block, cfg)

    result = rule_pattern.format(rule.name, var_decls, body, out_var,
                                 name_to_enum(rule.name))
    print(result)
    return result


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

    return rule_printer_pattern.format(name_to_enum(rule.name),
                                       name_to_enum(rule.name).lower(),
                                       params_str)


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
    return format_cpp(
        printer_pattern.format('\n'.join(
            gen_rule_printer(rule) for rule in rules)))


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
    else:  # if sort.base == BaseSort.BitVec:
        return '(term (BitVec n))'


def expr_to_lfsc(expr):
    if isinstance(expr, Fn):
        if expr.op in [Op.ZERO_EXTEND]:
            args = [expr_to_lfsc(arg) for arg in expr.children]
            return '({} zebv {} _ {})'.format(
                op_to_lfsc[expr.op], ' '.join(args[:op_to_nindex[expr.op]]),
                ' '.join(args[op_to_nindex[expr.op]:]))
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

    print(
        rule_pattern.format(rule_name, '\n'.join(varargs), lhs, rhs,
                            closing_parens))


def type_check(rules):
    for rule in rules:
        infer_types(rule.rvars, rule.lhs)
        infer_types(rule.rvars, rule.rhs)

        # Ensure that we were able to compute the types for both sides
        assert isinstance(rule.lhs.sort, Sort) and isinstance(
            rule.rhs.sort, Sort)


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
    #args.printerfile.write(gen_proof_printer(rules))

    #for rule in rules:
    #    rule_to_lfsc(rule)


if __name__ == "__main__":
    main()
