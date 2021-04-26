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
    Op.BVUGT: "BITVECTOR_UGT",
    Op.BVUGE: "BITVECTOR_UGE",
    Op.BVSGT: "BITVECTOR_SGT",
    Op.BVSGE: "BITVECTOR_SGE",
    Op.BVSLT: "BITVECTOR_SLT",
    Op.BVSLE: "BITVECTOR_SLE",
    Op.BVULT: "BITVECTOR_ULT",
    Op.BVULE: "BITVECTOR_ULE",
    Op.BVREDAND: "BITVECTOR_REDAND",
    Op.BVREDOR: "BITVECTOR_REDOR",
    Op.BVNEG: "BITVECTOR_NEG",
    Op.BVADD: "BITVECTOR_PLUS",
    Op.BVSUB: "BITVECTOR_SUB",
    Op.BVMUL: "BITVECTOR_MULT",
    Op.BVSDIV: "BITVECTOR_SDIV",
    Op.BVUDIV: "BITVECTOR_UDIV_TOTAL",
    Op.BVSREM: "BITVECTOR_SREM",
    Op.BVUREM: "BITVECTOR_UREM_TOTAL",
    Op.BVSMOD: "BITVECTOR_SMOD",
    Op.BVSHL: "BITVECTOR_SHL",
    Op.BVLSHR: "BITVECTOR_LSHR",
    Op.BVASHR: "BITVECTOR_ASHR",
    Op.ROTATE_LEFT: "BITVECTOR_ROTATE_LEFT",
    Op.ROTATE_RIGHT: "BITVECTOR_ROTATE_RIGHT",
    Op.BVNOT: "BITVECTOR_NOT",
    Op.BVAND: "BITVECTOR_AND",
    Op.BVOR: "BITVECTOR_OR",
    Op.BVXOR: "BITVECTOR_XOR",
    Op.BVNAND: "BITVECTOR_NAND",
    Op.BVNOR: "BITVECTOR_NOR",
    Op.BVXNOR: "BITVECTOR_XNOR",
    Op.CONCAT: "BITVECTOR_CONCAT",
    Op.BVITE: "BITVECTOR_ITE",
    Op.BVCOMP: "BITVECTOR_COMP",
    Op.BVCONST: "CONST_BITVECTOR",
    Op.ZERO_EXTEND: "BITVECTOR_ZERO_EXTEND",
    Op.SIGN_EXTEND: "BITVECTOR_SIGN_EXTEND",
    Op.EXTRACT: "BITVECTOR_EXTRACT",
    Op.REPEAT: "BITVECTOR_REPEAT",
    Op.NOT: "NOT",
    Op.AND: "AND",
    Op.OR: "OR",
    Op.XOR: "XOR",
    Op.EQ: "EQUAL",
    Op.ITE: "ITE",
}

op_to_const_eval = {
    Op.BVSHL: lambda args: "({}.leftShift({}))".format(args[0], args[1]),
    Op.BVNEG: lambda args: "(-{})".format(args[0]),
    Op.BVULE: lambda args: f"({args[0]} <= {args[1]})",
    Op.BVUGE: lambda args: f"({args[0]} >= {args[1]})",
    Op.BVULT: lambda args: f"({args[0]} < {args[1]})",
    Op.EXTRACT: lambda args: "({2}.extract({0}, {1}))".format(*args),
    Op.BVNOT: lambda args: "(~{})".format(args[0]),
    Op.BVAND: lambda args: "({} & {})".format(args[0], args[1]),
    Op.BVOR: lambda args: "({} | {})".format(args[0], args[1]),
    Op.BVXOR: lambda args: "({} ^ {})".format(args[0], args[1]),
    Op.CONCAT: lambda args: "({}.concat({}))".format(args[0], args[1]),
    Op.PLUS: lambda args: "({} + {})".format(args[0], args[1]),
    Op.MINUS: lambda args: "({} - {})".format(args[0], args[1]),
    Op.MULT: lambda args: "({} * {})".format(args[0], args[1]),
    Op.LEQ: lambda args: "({} <= {})".format(args[0], args[1]),
    Op.LT: lambda args: "({} < {})".format(args[0], args[1]),
    Op.GEQ: lambda args: "({} >= {})".format(args[0], args[1]),
    Op.NOT: lambda args: "(!{})".format(args[0]),
    Op.AND: lambda args: "({})".format(" && ".join(args)) if len(args) > 0 else "true",
    Op.OR: lambda args: "({})".format(" || ".join(args)) if len(args) > 0 else "true",
    Op.EQ: lambda args: "({} == {})".format(args[0], args[1]),
    Op.ZEROES: lambda args: "bv::utils::zeroes({})".format(args[0]),
    Op.POW2: lambda args: "bv::utils::isPow2Const({})".format(args[0]),
    Op.NPOW2: lambda args: "bv::utils::isNegPow2Const({})".format(args[0]),
}

op_to_lfsc = {
    Op.BVUGT: "bvugt",
    Op.BVUGE: "bvuge",
    Op.BVSGT: "bvsgt",
    Op.BVSGE: "bvsge",
    Op.BVSLT: "bvslt",
    Op.BVSLE: "bvsle",
    Op.BVULT: "bvult",
    Op.BVULE: "bvule",
    Op.BVNEG: "bvneg",
    Op.BVADD: "bvadd",
    Op.BVSUB: "bvsub",
    Op.CONCAT: "concat",
    Op.ZERO_EXTEND: "zero_extend",
    Op.NOT: "not",
    Op.EQ: "=",
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
    instr_block = fresh_name("block")
    if next_block:
        cfg[instr_block] = CFGNode([instr], [CFGEdge(BoolConst(True), next_block)])
    else:
        cfg[instr_block] = CFGNode([instr], [])
    return instr_block


def rule_to_in_ir(cfg, out_block, node_var, rvars, lhs):
    def expr_to_ir(const_checks, next_block, expr, node, vars_seen, in_loop=False):
        if isinstance(expr, Var):
            if expr.name in vars_seen:
                return mk_simple_block(
                    cfg, next_block, Assert(Fn(Op.EQ, [expr, node]), in_loop)
                )
            else:
                if expr.sort is not None and expr.sort.base == BaseSort.BitVec:
                    width = expr.sort.children[0]
                    if isinstance(width, Var) and not width.name in vars_seen:
                        bv_size_expr = Fn(Op.BV_SIZE, [node])
                        bv_size_expr.sort = Sort(BaseSort.Int, [], True)
                        # TODO: should resolve earlier?
                        width.sort = Sort(BaseSort.Int, [], True)
                        next_block = mk_simple_block(
                            cfg, next_block, Assign(width, bv_size_expr)
                        )
                        vars_seen.add(width.name)

                next_block = mk_simple_block(cfg, next_block, Assign(expr, node))

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

                if (
                    isinstance(expr.children[0], Var)
                    and expr.children[0].name not in vars_seen
                ):
                    next_block = mk_simple_block(
                        cfg,
                        next_block,
                        Assign(expr.children[0], Fn(Op.BV_SIZE, [node])),
                    )

                    next_block = expr_to_ir(
                        const_checks,
                        next_block,
                        expr.children[0],
                        Fn(Op.BV_SIZE, [node]),
                        vars_seen,
                        in_loop,
                    )

                if (
                    isinstance(expr.children[1], Var)
                    and expr.children[1].name not in vars_seen
                ):
                    next_block = expr_to_ir(
                        const_checks,
                        next_block,
                        expr.children[1],
                        Fn(Op.BV_SIZE, [node]),
                        vars_seen,
                        in_loop,
                    )

                next_block = mk_simple_block(
                    cfg,
                    next_block,
                    Assert(
                        Fn(Op.EQ, [Fn(Op.GET_KIND, [node]), KindConst(expr.op)]),
                        in_loop,
                    ),
                )

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
                    child for child in expr.children if child.sort.base != BaseSort.List
                ]
                loop_idxs = [
                    Var(fresh_name("loopi"), Sort(BaseSort.Int32, [], True))
                    for _ in nlist_children
                ]

                # Assign the remainder of the list
                if len(nlist_children) != len(expr.children):
                    list_child = next(
                        child
                        for child in expr.children
                        if child.sort.base == BaseSort.List
                    )
                    print(loop_idxs)
                    cond = Fn(
                        Op.AND,
                        [
                            Fn(
                                Op.NOT,
                                [
                                    Fn(
                                        Op.EQ,
                                        [Var("i", Sort(BaseSort.Int32, [], True)), idx],
                                    )
                                ],
                            )
                            for idx in loop_idxs
                        ],
                    )

                    # TODO: Do at creation-time
                    cond.sort = Sort(BaseSort.Bool, [], True)
                    for child in cond.children:
                        child.sort = Sort(BaseSort.Bool, [], True)
                        child.children[0].sort = Sort(BaseSort.Bool, [], True)

                    next_block = mk_simple_block(
                        cfg,
                        next_block,
                        Assign(list_child, Fn(Op.GET_CHILDREN, [node, cond])),
                    )

                for i, child in reversed(list(enumerate(nlist_children))):
                    sub_expr_vars_seen = vars_seen.copy()
                    for child2 in nlist_children[:i]:
                        sub_expr_vars_seen |= collect_vars(child2)

                    loop_idx = loop_idxs[i]
                    loop_var_sort = Sort(child.sort.base, child.sort.children)
                    loop_var = Var(fresh_name("loopv"), loop_var_sort)
                    next_block = expr_to_ir(
                        const_checks,
                        next_block,
                        child,
                        loop_var,
                        sub_expr_vars_seen,
                        True,
                    )
                    next_block = mk_simple_block(
                        cfg,
                        next_block,
                        Assign(loop_var, Fn(Op.GET_CHILD, [node, loop_idx])),
                    )

                    for j in range(i):
                        check = Fn(Op.NOT, [Fn(Op.EQ, [loop_idx, loop_idxs[j]])])
                        # Use infer types
                        check.sort = Sort(BaseSort.Bool, [], True)
                        check.children[0].sort = Sort(BaseSort.Bool, [], True)
                        next_block = mk_simple_block(
                            cfg, next_block, Assert(check, True)
                        )

                    loop_block = fresh_name("loop")
                    cfg[loop_block] = CFGLoop(loop_idx, node, next_block)
                    next_block = loop_block
            elif expr.op in associative_ops:
                nlist_children = [
                    child for child in expr.children if child.sort.base != BaseSort.List
                ]
                loop_idxs = [
                    (
                        Var(fresh_name("loopi"), Sort(BaseSort.Int32, [], True))
                        if child.sort.base != BaseSort.List
                        else None
                    )
                    for child in expr.children
                ]

                # Assign the list children
                if len(nlist_children) != len(expr.children):
                    for i, child in enumerate(expr.children):
                        if child.sort.base != BaseSort.List:
                            continue

                        var_i = Var("i", Sort(BaseSort.Int32, [], True))
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
                            cfg,
                            next_block,
                            Assign(child, Fn(Op.GET_CHILDREN, [node, cond])),
                        )

                for i, child in reversed(list(enumerate(expr.children))):
                    if child.sort and child.sort.base == BaseSort.List:
                        continue

                    sub_expr_vars_seen = vars_seen.copy()
                    for child2 in expr.children[: i - 1]:
                        sub_expr_vars_seen |= collect_vars(child2)

                    loop_idx = loop_idxs[i]
                    loop_var_sort = Sort(child.sort.base, child.sort.children)
                    loop_var = Var(fresh_name("loopv"), loop_var_sort)
                    next_block = expr_to_ir(
                        const_checks,
                        next_block,
                        child,
                        loop_var,
                        sub_expr_vars_seen,
                        True,
                    )
                    next_block = mk_simple_block(
                        cfg,
                        next_block,
                        Assign(loop_var, Fn(Op.GET_CHILD, [node, loop_idx])),
                    )

                    for j in range(i):
                        if not loop_idxs[j]:
                            continue

                        check = Fn(Op.LT, [loop_idxs[j], loop_idx])
                        # Use infer types
                        check.sort = Sort(BaseSort.Bool, [], True)
                        next_block = mk_simple_block(
                            cfg, next_block, Assert(check, True)
                        )

                    loop_block = fresh_name("loop")
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
                        child_node.sort = Sort(BaseSort.Int32, [], True)
                    else:
                        child_node = Fn(
                            Op.GET_CHILD, [node, IntConst(i - op_to_nindex[expr.op])]
                        )
                    next_block = expr_to_ir(
                        const_checks,
                        next_block,
                        child,
                        child_node,
                        sub_expr_vars_seen,
                        in_loop,
                    )

            return mk_simple_block(
                cfg,
                next_block,
                Assert(
                    Fn(Op.EQ, [Fn(Op.GET_KIND, [node]), KindConst(expr.op)]), in_loop
                ),
            )

        elif isinstance(expr, BVConst):
            assert False
            next_block = mk_simple_block(
                cfg,
                next_block,
                Assert(Fn(Op.EQ, [GetChild(path), Fn(Op.MK_CONST, [expr])]), in_loop),
            )

            if isinstance(expr.bw, Var) and not expr.bw.name in vars_seen:
                bv_size_expr = Fn(Op.BV_SIZE, [GetChild(path)])
                bv_size_expr.sort = Sort(BaseSort.Int, [])
                next_block = mk_simple_block(
                    cfg, next_block, Assign(expr.bw.name, bv_size_expr)
                )
                vars_seen.add(expr.bw.name)

            return next_block

        print("Unsupported {}".format(expr))
        assert False

    vars_seen = set()
    const_check_block = fresh_name("block")
    const_checks = []
    entry = expr_to_ir(const_checks, const_check_block, lhs, node_var, vars_seen)
    cfg[const_check_block] = CFGNode(
        const_checks, [CFGEdge(BoolConst(True), out_block)]
    )
    return entry


def rule_to_out_expr(cfg, next_block, res, expr):
    def expr_to_out_expr(expr):
        if isinstance(expr, Fn):
            new_args = []
            for i, child in enumerate(expr.children):
                child_expr = expr_to_out_expr(child)
                if (
                    i >= op_to_nindex[expr.op]
                    and not expr.sort.const
                    and child.sort.const
                ):
                    child_expr = Fn(Op.MK_CONST, [child_expr])
                new_args.append(child_expr)
            return Fn(Op.MK_NODE, [KindConst(expr.op)] + new_args)
        else:
            return expr

    def rule_to_out_expr_rec(cfg, next_block, res, expr):
        if isinstance(expr, Fn):
            if expr.op == Op.COND:
                cases = []
                for case in expr.children:
                    cond = case.children[0]
                    result = rule_to_out_expr(cfg, None, res, case.children[1])
                    cases.append((cond, result))
                return CFGCond(cases)
            elif expr.op == Op.FAIL:
                return CFGSeq([Assert(BoolConst(False), False)])
            elif expr.op == Op.LET:
                assign = rule_to_out_expr(cfg, None, expr.children[0], expr.children[1])
                body = rule_to_out_expr(cfg, None, res, expr.children[2])
                return CFGSeq([assign, body])
            elif expr.op == Op.MAP:
                body = expr_to_out_expr(expr.children[0].children[1])
                assign = Assign(
                    res,
                    Fn(
                        Op.MAP,
                        [
                            Fn(Op.LAMBDA, [expr.children[0].children[0], body]),
                            expr.children[1],
                        ],
                    ),
                )
                return CFGSeq([assign])
            elif expr.op == Op.BVCONST:
                new_vars = [
                    Var(fresh_name("__v"), child.sort) for child in expr.children
                ]
                print(expr, new_vars, [c.sort for c in new_vars])
                bvc = Fn(Op.BVCONST, new_vars)
                bvc.sort = expr.sort
                assign = None
                if res.sort and res.sort.const:
                    assign = Assign(res, bvc)
                else:
                    mk_const = Fn(Op.MK_CONST, [bvc])
                    mk_const.sort = Sort(bvc.sort.base, bvc.sort.children)
                    assign = Assign(res, mk_const)

                args = []
                for var, child in zip(new_vars, expr.children):
                    args.append(rule_to_out_expr(cfg, None, var, child))
                print(expr, new_vars, [c.sort for c in new_vars])
                # assign_block = fresh_name('block')
                # if next_block:
                #     cfg[assign_block] = CFGNode(
                #         [assign], [CFGEdge(BoolConst(True), next_block)])
                # else:
                #     cfg[assign_block] = CFGNode([assign], [])

                # next_block = assign_block
                # for var, child in zip(new_vars, expr.children):
                #     next_block = rule_to_out_expr(cfg, next_block, var, child)
                return CFGSeq(args + [assign])
            else:
                new_vars = [
                    Var(fresh_name("__v"), child.sort) for child in expr.children
                ]

                args = []
                for var, child in zip(new_vars, expr.children):
                    args.append(rule_to_out_expr(cfg, None, var, child))

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
                            mk_const.sort = Sort(
                                new_var.sort.base, new_var.sort.children
                            )
                            new_args.append(mk_const)
                        else:
                            new_args.append(new_var)

                    assign = Assign(
                        res, Fn(Op.MK_NODE, [KindConst(expr.op)] + new_args)
                    )

                return CFGSeq(args + [assign])
        elif isinstance(expr, BoolConst):
            assign_block = fresh_name("block")
            res.sort = Sort(BaseSort.Bool, [])
            assign = Assign(res, Fn(Op.MK_CONST, [expr]))
            return CFGSeq([assign])
        elif isinstance(expr, IntConst):
            assign_block = fresh_name("block")
            res.sort = Sort(res.sort.base, [], True)
            assign = Assign(res, expr)
            if next_block:
                cfg[assign_block] = CFGNode(
                    [assign], [CFGEdge(BoolConst(True), next_block)]
                )
            else:
                cfg[assign_block] = CFGNode([assign], [])
            return CFGSeq([assign])
        elif isinstance(expr, Var):
            assign_block = fresh_name("block")
            assign = Assign(res, expr)
            res.sort = expr.sort
            if next_block:
                cfg[assign_block] = CFGNode(
                    [assign], [CFGEdge(BoolConst(True), next_block)]
                )
            else:
                cfg[assign_block] = CFGNode([assign], [])
            return CFGSeq([assign])  # assign_block
        else:
            return expr

    return rule_to_out_expr_rec(cfg, next_block, res, expr)


def default_val(kind, sort):
    if kind in [Op.BVADD, Op.BVOR, Op.BVXOR]:
        print(kind)
        n = (
            sort.children[0].children[0]
            if sort.base == BaseSort.List
            else sort.children[0]
        )
        ret = Fn(Op.MK_CONST, [BVConst(0, n)])
        ret.sort = Sort(BaseSort.BitVec, [n], True)
        return ret
    elif kind == Op.BVMUL:
        n = (
            sort.children[0].children[0]
            if sort.base == BaseSort.List
            else sort.children[0]
        )
        ret = Fn(Op.MK_CONST, [BVConst(1, n)])
        ret.sort = Sort(BaseSort.BitVec, [n], True)
        return ret
    elif kind == Op.BVAND:
        n = (
            sort.children[0].children[0]
            if sort.base == BaseSort.List
            else sort.children[0]
        )
        not_zero = Fn(Op.BVNOT, [BVConst(0, n)])
        not_zero.sort = Sort(BaseSort.BitVec, [n], True)
        ret = Fn(Op.MK_CONST, [not_zero])
        ret.sort = Sort(BaseSort.BitVec, [n], True)
        return ret
    elif kind in [Op.CONCAT]:
        ret = Fn(Op.MK_CONST, [BVConst(0, IntConst(0))])
        ret.sort = Sort(BaseSort.BitVec, [IntConst(0)], True)
        return ret

    print(f"Missing default case (kind = {kind}, sort = {sort})")
    assert False


def expr_to_code(expr):
    if isinstance(expr, Fn):
        args = [expr_to_code(child) for child in expr.children]

        if expr.op == Op.EQ:
            return "({} == {})".format(args[0], args[1])
        elif expr.op == Op.GET_KIND:
            return f"{args[0]}.getKind()"
        elif expr.op == Op.IS_BITVECTOR_NODE:
            return f"{args[0]}.getType().isBitVector()"
        elif expr.op == Op.GET_NUM_CHILDREN:
            return f"{args[0]}.getNumChildren()"
        elif expr.op == Op.BV_SIZE:
            return "bv::utils::getSize({})".format(args[0])
        elif expr.op == Op.BV_VAL:
            return f"({args[0]}).getValue()"
        elif expr.op == Op.BVCONST:
            val = f"Integer({args[0]})" if expr.children[0].sort.base == BaseSort.Int32 else args[0]
            width = f"{args[1]}.getUnsignedInt()" if expr.children[1].sort.base == BaseSort.Int else args[1]
            return f"BitVector({width}, {val})"
        elif expr.op == Op.GET_CONST:
            sort = expr.children[0].sort
            const_sort = Sort(sort.base, sort.children, True)
            return f"{args[0]}.getConst<{sort_to_code(const_sort)}>()"
        elif expr.op == Op.MK_CONST:
            return "nm->mkConst({})".format(", ".join(args))
        elif expr.op == Op.MK_NODE:
            kind = expr.children[0].val

            has_list_arg = False
            for child in expr.children:
                if child.sort and child.sort.base == BaseSort.List:
                    has_list_arg = True
                    break

            arg_str = None
            if has_list_arg:
                vec = fresh_name("__vec")
                default = expr_to_code(
                    default_val(expr.children[0].val, expr.children[1].sort)
                )
                ret = f"{vec}.size() == 0 ? {default} : ({vec}.size() == 1 ? {vec}[0] : nm->mkNode({args[0]}, {vec}))"
                return "[&](){{ std::vector<Node> {0}; {1}; return {2}; }}()".format(
                    vec,
                    ";".join(
                        (
                            "{}.push_back({})".format(vec, arg)
                            if child.sort and child.sort.base != BaseSort.List
                            else "{0}.insert({0}.end(), {1}.begin(), {1}.end())".format(
                                vec, arg
                            )
                        )
                        for arg, child in zip(args[1:], expr.children[1:])
                    ),
                    ret,
                )

            if op_to_nindex[kind] != 0:
                # Convert Integer to uint32_t for indices
                for i, arg in enumerate(args[: op_to_nindex[kind] + 1]):
                    if expr.children[i].sort and expr.children[i].sort.base == BaseSort.Int:
                        args[i] = f"{arg}.getUnsignedInt()"

                op = "bv::utils::mkIndexedOp({})".format(
                    ", ".join(args[: op_to_nindex[kind] + 1])
                )
                arg_str = ", ".join([op] + args[op_to_nindex[kind] + 1 :])
            else:
                arg_str = ", ".join(args)

            return "nm->mkNode({})".format(arg_str)
        elif expr.op == Op.IS_NULL:
            return f"({args[0]}).isNull()"
        elif expr.op == Op.GET_CHILD:
            return "{}[{}]".format(args[0], args[1])
        elif expr.op == Op.GET_CHILDREN:
            if len(args) == 1:
                return "std::vector<Node>({0}.begin(), {0}.end())".format(args[0])
            else:
                return f"bv::utils::getChildren({args[0]}, [&](size_t {args[1]}) {{ return {args[2]}; }})"
        elif expr.op == Op.SLICE:
            if len(args) == 2:
                return (
                    f"std::vector<Node>({args[0]}.begin() + {args[1]}, {args[0]}.end())"
                )
            else:
                return f"std::vector<Node>({args[0]}.begin() + {args[1]}, {args[0]}.begin() + {args[2]})"
        elif expr.op == Op.GET_INDEX:
            return "bv::utils::getIndex({}, {})".format(args[0], args[1])
        elif expr.sort and expr.sort.const:
            if expr.sort.base == BaseSort.Int:
                for i, arg in enumerate(args):
                    if expr.children[i].sort and expr.children[i].sort.base == BaseSort.Int32:
                        args[i] = f"Integer({arg})"
            return op_to_const_eval[expr.op](args)
        elif expr.op == Op.MAP:
            return "bv::utils::mapVector({}, {})".format(args[1], args[0])
        elif expr.op == Op.LAMBDA:
            return "[&]({} {}) {{ return {}; }}".format(
                sort_to_code(expr.children[0].sort), args[0], args[1]
            )
        else:
            print(
                "No code generation for op {} in {} (sort {})".format(
                    expr.op, expr, expr.sort
                )
            )
            assert False
    elif isinstance(expr, BoolConst):
        return "true" if expr.val else "false"
    elif isinstance(expr, BVConst):
        bw_code = expr_to_code(expr.bw)
        return "BitVector({}, Integer({}))".format(bw_code, expr.val)
    elif isinstance(expr, IntConst):
        return str(expr.val)
    elif isinstance(expr, KindConst):
        return "kind::{}".format(op_to_kind[expr.val])
    elif isinstance(expr, Var):
        return expr.name


def sort_to_code(sort):
    if not sort or not sort.const:
        # TODO: null sort should not happen
        if sort.base == BaseSort.List:
            return "std::vector<{}>".format(sort_to_code(sort.children[0]))
        else:
            return "Node"
    elif sort.base == BaseSort.Int:
        return "Integer"
    elif sort.base == BaseSort.Int32:
        return "uint32_t"
    elif sort.base == BaseSort.BitVec:
        return "BitVector"


def ir_to_code(name, match_instrs):
    code = []
    for instr in match_instrs:
        if isinstance(instr, Assign):
            code.append("{} = {};".format(instr.name, expr_to_code(instr.expr)))
        elif isinstance(instr, Assert):
            exit = (
                "continue"
                if instr.in_loop
                else "return RewriteResponse(REWRITE_DONE, __node, RewriteRule::NONE)"
            )
            code_str = f"""
            if (!({expr_to_code(instr.expr)})) {{
              {exit};
            }}
            """.strip()
            code.append(code_str)
        elif isinstance(instr, Return):
            code.append(
                f"return RewriteResponse(REWRITE_AGAIN, {expr_to_code(instr.expr)}, RewriteRule::{name});"
            )
        elif isinstance(instr, CFGSeq):
            code.append(ir_to_code(name, instr.instrs))
        elif isinstance(instr, CFGCond):
            first = True
            for case in instr.cases:
                keyword = "if" if first else "else if"
                first = False
                code_str = f"""
                {keyword} ({expr_to_code(case[0])}) {{
                  {ir_to_code(name, [case[1]])}
                }}
                """.strip()
                code.append(code_str)
        elif isinstance(instr, CFGLoop):
            code.append(cfg_to_code(name, instr, None))
        else:
            print(f"No code generation for {instr}")
            assert False

    return "\n".join(code)


def cfg_to_code(name, block, cfg):
    if isinstance(block, CFGLoop):
        body = cfg_to_code(name, block.body, cfg)
        return """
        for ({} = 0; {} < {}; {}++) {{
         {}
        }}""".format(
            block.loop_var,
            block.loop_var,
            expr_to_code(block.domain),
            block.loop_var,
            body,
        )
    else:
        result = ir_to_code(name, block.instrs)
        # first_edge = True
        # for edge in block.edges:
        #     branch_code = cfg_to_code(edge.target, cfg)

        #     if edge.cond == BoolConst(True):
        #         if first_edge:
        #             result += branch_code
        #         else:
        #             result += """
        #             else {{
        #               {}
        #             }}""".format(branch_code)
        #         break
        #     else:
        #         cond_type = 'if' if first_edge else 'else if'

        #         result += """
        #         {} ({}) {{
        #          {}
        #         }}""".format(cond_type, expr_to_code(edge.cond), branch_code)

        #     first_edge = False
        return result


def name_to_enum(name):
    name = re.sub(r"(?<!^)(?=[A-Z])", "_", name).upper()
    return name


def gen_rule_old(rule):
    node_var = Var("__node", rule.lhs.sort)
    out_var = Var("__ret", Sort(rule.rhs.sort.base, rule.rhs.sort.children))

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
    var_decls = ""
    for var in cfg_vars:
        var_decls += "{} {};\n".format(sort_to_code(var.sort), var.name)

    body = cfg_to_code(rule.name, match_block, cfg)

    result = f"""
    inline RewriteResponse {rule.name}(TNode __node) {{
      NodeManager* nm = NodeManager::currentNM();
      {var.decls}
      {body}
      return RewriteResponse(REWRITE_AGAIN, {out_var}, RewriteRule::{name_to_enum(rule.name)});
    }}"""
    return result


def rule_to_match_ir(cfg, out_block, node_var, out_var, lhs):
    def expr_to_ir(
        expr, node, match_instrs, const_match_instrs, vars_seen, in_loop, last
    ):
        if expr.sort.base == BaseSort.BitVec:
            match_instrs.append(Assert(Fn(Op.IS_BITVECTOR_NODE, [node]), in_loop))
            width = expr.sort.children[0]
            if isinstance(width, Var) and not width.name in vars_seen:
                bv_size_expr = Fn(Op.BV_SIZE, [node])
                bv_size_expr.sort = Sort(BaseSort.Int32, [], True)
                width.sort = Sort(BaseSort.Int32, [], True)
                match_instrs.append(Assign(width, bv_size_expr))
                vars_seen.add(width.name)
            elif isinstance(width, IntConst):
                bv_size_expr = Fn(Op.BV_SIZE, [node])
                bv_size_expr.sort = Sort(BaseSort.Int32, [], True)
                width.sort = Sort(BaseSort.Int32, [], True)
                match_instrs.append(Assert(Fn(Op.EQ, [bv_size_expr, width]), in_loop))

        if isinstance(expr, Var):
            node_val = node
            if expr.sort.const and (
                not isinstance(node, Fn) or node.op != Op.GET_INDEX
            ):
                match_instrs.append(
                    Assert(
                        Fn(Op.EQ, [Fn(Op.GET_KIND, [node]), KindConst(Op.BVCONST)]),
                        in_loop,
                    )
                )
                node_val = Fn(Op.GET_CONST, [node])

            if expr.name in vars_seen:
                match_instrs.append(Assert(Fn(Op.EQ, [node_val, expr]), in_loop))
            else:
                if expr.sort is not None and expr.sort.base == BaseSort.BitVec:
                    width = expr.sort.children[0]
                    if isinstance(width, Var) and not width.name in vars_seen:
                        bv_size_expr = Fn(Op.BV_SIZE, [node])
                        bv_size_expr.sort = Sort(BaseSort.Int32, [], True)
                        # TODO: should resolve earlier?
                        width.sort = Sort(BaseSort.Int32, [], True)
                        match_instrs.append(Assign(width, bv_size_expr))
                        vars_seen.add(width.name)

                match_instrs.append(Assign(expr, node_val))
                vars_seen.add(expr.name)
        else:
            expr_var = Var(expr.name, expr.sort)
            if expr.sort.const:
                # if isinstance(expr, Fn) and expr.op == Op.BVCONST:
                #     if isinstance(expr.children[0], Var) and expr.children[0] not in vars_seen:
                #         match_instrs.append(Assert(Fn(Op.EQ, [Fn(Op.GET_KIND, [expr.name]), KindConst(expr.op)]), False))
                #         if isinstance(expr.children[0], Var) and expr.children[0].name not in vars_seen:
                #             v = expr.children[0]
                #             match_instrs.append(Assign(v, Fn(Op.BV_SIZE, [node])))

                #         #next_block = mk_simple_block(
                #         #    cfg, next_block,
                #         #    Assign(expr.children[0], Fn(Op.BV_SIZE, [node])))

                #         #next_block = expr_to_ir(const_checks, next_block,
                #         #                        expr.children[0],
                #         #                        Fn(Op.BV_SIZE,
                #         #                           [node]), vars_seen, in_loop)
                #         return
                # else:
                if (
                    isinstance(expr, Fn)
                    and expr.op == Op.BVCONST
                    and isinstance(expr.children[0], Var)
                    and expr.children[0].name not in vars_seen
                ):
                    kind_const = KindConst(Op.BVCONST)
                    match_instrs.append(
                        Assert(
                            Fn(Op.EQ, [Fn(Op.GET_KIND, [node]), kind_const]),
                            in_loop,
                        )
                    )
                    match_instrs.append(Assign(expr_var, Fn(Op.GET_CONST, [node])))
                    match_instrs.append(
                        Assign(expr.children[0], Fn(Op.BV_VAL, [expr_var]))
                    )
                    vars_seen.add(expr.children[0].name)
                else:
                    if isinstance(node, Fn) and node.op == Op.GET_INDEX:
                        match_instrs.append(Assign(expr_var, node))
                    else:
                        assert expr.sort.base == BaseSort.BitVec
                        kind_const = KindConst(Op.BVCONST)
                        match_instrs.append(
                            Assert(
                                Fn(Op.EQ, [Fn(Op.GET_KIND, [node]), kind_const]),
                                in_loop,
                            )
                        )
                        match_instrs.append(Assign(expr_var, Fn(Op.GET_CONST, [node])))
                    const_match_instrs.append(
                        Assert(Fn(Op.EQ, [expr_var, expr]), in_loop)
                    )
            else:
                match_instrs.append(Assign(expr_var, node))
                if isinstance(expr, Fn):
                    match_instrs.append(
                        Assert(
                            Fn(
                                Op.EQ,
                                [
                                    Fn(Op.GET_KIND, [Var(expr.name, expr.sort)]),
                                    KindConst(expr.op),
                                ],
                            ),
                            in_loop,
                        )
                    )

                    # Commutative and associative ops
                    if expr.op in commutative_ops and expr.op in associative_ops:
                        nlist_children = [
                            child
                            for child in expr.children
                            if child.sort.base != BaseSort.List
                        ]
                        loop_idxs = [
                            Var(fresh_name("loopi"), Sort(BaseSort.Int32, [], True))
                            for _ in nlist_children
                        ]

                        # Expression for assigning the remainder of the list
                        remainder_expr = None
                        if len(nlist_children) != len(expr.children):
                            var = Var("i", Sort(BaseSort.Int32, [], True))
                            list_child = next(
                                child
                                for child in expr.children
                                if child.sort.base == BaseSort.List
                            )
                            cond = Fn(
                                Op.AND,
                                [
                                    Fn(Op.NOT, [Fn(Op.EQ, [var, idx])])
                                    for idx in loop_idxs
                                ],
                            )

                            # TODO: Do at creation-time
                            cond.sort = Sort(BaseSort.Bool, [], True)
                            for child in cond.children:
                                child.sort = Sort(BaseSort.Bool, [], True)
                                child.children[0].sort = Sort(BaseSort.Bool, [], True)

                            remainder_expr = Assign(
                                list_child, mk_node(Op.GET_CHILDREN, node, var, cond)
                            )

                        has_non_remainder = len(nlist_children) != 0
                        last = last and (not has_non_remainder)
                        curr_block = match_instrs

                        if expr.op in nary_ops and len(nlist_children) == len(expr.children):
                            curr_block.append(
                                Assert(
                                    Fn(
                                        Op.EQ,
                                        [
                                            Fn(Op.GET_NUM_CHILDREN, [node]),
                                            IntConst(len(nlist_children)),
                                        ],
                                    ),
                                    in_loop,
                                )
                            )

                        prev_in_loop = in_loop
                        for i, child in list(enumerate(nlist_children)):
                            loop_idx = loop_idxs[i]
                            loop_var_sort = Sort(child.sort.base, child.sort.children)
                            loop_var = Var(fresh_name("loopv"), loop_var_sort)

                            # Get child node for loop index
                            loop_body = [
                                Assign(loop_var, Fn(Op.GET_CHILD, [node, loop_idx]))
                            ]

                            for j in range(i):
                                check = Fn(
                                    Op.NOT, [Fn(Op.EQ, [loop_idx, loop_idxs[j]])]
                                )
                                # Use infer types
                                check.sort = Sort(BaseSort.Bool, [], True)
                                check.children[0].sort = Sort(BaseSort.Bool, [], True)

                                # Skip children already assigned to loop indices
                                loop_body.append(Assert(check, True))

                            last_child = i == len(nlist_children) - 1
                            if last_child and remainder_expr:
                                loop_body.append(remainder_expr)

                            expr_to_ir(
                                child,
                                loop_var,
                                loop_body,
                                const_match_instrs,
                                vars_seen,
                                True,
                                last=last_child,
                            )

                            curr_block.append(
                                CFGLoop(
                                    loop_idx,
                                    mk_node(Op.GET_NUM_CHILDREN, node),
                                    CFGSeq(loop_body),
                                )
                            )
                            if i != 0:
                                curr_block.append(
                                    Assert(Fn(Op.EQ, [node_var, out_var]), True)
                                )
                            curr_block = loop_body

                        if has_non_remainder:
                            curr_block.append(
                                Assert(Fn(Op.EQ, [node_var, out_var]), True)
                            )
                        else:
                            # If we only have a list argument, e.g. (bvadd xs)
                            curr_block.append(remainder_expr)

                        if has_non_remainder and not prev_in_loop:
                            match_instrs.append(Assert(BoolConst(False), False))
                    elif expr.op in associative_ops:
                        nlist_children = [
                            child
                            for child in expr.children
                            if child.sort.base != BaseSort.List
                        ]

                        next_idx = IntConst(0)
                        curr_block = match_instrs
                        prev_in_loop = in_loop
                        for i, child in list(enumerate(expr.children)):
                            last_child = i == len(expr.children) - 1
                            if child.sort.base == BaseSort.List:
                                if last_child:
                                    continue

                                in_loop = True
                                var_i = Var(
                                    fresh_name("loopi"), Sort(BaseSort.Int32, [], True)
                                )
                                conds = []
                                loop_body = []
                                if i != 0:
                                    cond = mk_node(Op.LEQ, next_idx, var_i)
                                    infer_types(None, cond)
                                    loop_body.append(Assert(cond, in_loop))

                                loop_body.append(
                                    Assign(child, Fn(Op.SLICE, [node, next_idx, var_i]))
                                )

                                if Op.CONCAT and isinstance(child.sort.children[0].children[0], Var):
                                    len_var = child.sort.children[0].children[0]
                                    list_node = Fn(Op.MK_NODE, [KindConst(Op.CONCAT), child])
                                    list_node.sort = Sort(BaseSort.BitVec, [len_var])
                                    list_len = Fn(Op.BV_SIZE, [list_node])
                                    loop_body.append(
                                        Assign(len_var, list_len)
                                    )

                                max_val = mk_node(
                                    Op.PLUS,
                                    mk_node(Op.GET_NUM_CHILDREN, node),
                                    IntConst(1),
                                )
                                next_idx = var_i
                                curr_block.append(
                                    CFGLoop(var_i, max_val, CFGSeq(loop_body))
                                )
                                curr_block = loop_body
                            else:
                                cond = mk_node(
                                    Op.LT, next_idx, mk_node(Op.GET_NUM_CHILDREN, node)
                                )

                                # Make sure that we are not out-of-bounds
                                curr_block.append(Assert(cond, in_loop))

                                loop_var_sort = Sort(
                                    child.sort.base, child.sort.children
                                )
                                loop_var = Var(fresh_name("loopv"), loop_var_sort)

                                # Get child node for loop index
                                curr_block.append(
                                    Assign(loop_var, Fn(Op.GET_CHILD, [node, next_idx]))
                                )

                                last_non_list_child = (
                                    i == len(expr.children) - 2
                                    and expr.children[-1].sort.base == BaseSort.List
                                )
                                if last_non_list_child:
                                    rhs = Fn(
                                        Op.SLICE,
                                        [node, Fn(Op.PLUS, [next_idx, IntConst(1)])],
                                    )
                                    infer_types(None, rhs)
                                    curr_block.append(Assign(expr.children[-1], rhs))

                                    # TODO: merge with other case
                                    remainder = expr.children[-1]
                                    if Op.CONCAT and isinstance(remainder.sort.children[0].children[0], Var):
                                        len_var = remainder.sort.children[0].children[0]
                                        list_node = Fn(Op.MK_NODE, [KindConst(Op.CONCAT), remainder])
                                        list_node.sort = Sort(BaseSort.BitVec, [len_var])
                                        list_len = Fn(Op.BV_SIZE, [list_node])
                                        curr_block.append(
                                            Assign(len_var, list_len)
                                        )
                                expr_to_ir(
                                    child,
                                    loop_var,
                                    curr_block,
                                    const_match_instrs,
                                    vars_seen,
                                    True,
                                    last=last and (last_child or last_non_list_child),
                                )
                                next_idx = mk_node(Op.PLUS, next_idx, IntConst(1))
                        if in_loop and not prev_in_loop:
                            match_instrs.append(Assert(BoolConst(False), False))
                        last = False
                    # Remaining ops
                    else:
                        for i, child in list(enumerate(expr.children)):
                            child_node = None
                            if i < op_to_nindex[expr.op]:
                                child_node = Fn(Op.GET_INDEX, [expr_var, IntConst(i)])
                                child_node.sort = Sort(BaseSort.Int32, [], True)
                            else:
                                child_node = Fn(
                                    Op.GET_CHILD,
                                    [expr_var, IntConst(i - op_to_nindex[expr.op])],
                                )
                                child_node.sort = expr.children[i].sort
                            expr_to_ir(
                                child,
                                child_node,
                                match_instrs,
                                const_match_instrs,
                                vars_seen,
                                in_loop=in_loop,
                                last=last and (i == len(expr.children) - 1),
                            )
                        last = False
                else:
                    print(f"No support for {expr}")
                    assert False

        if last:
            match_instrs.extend(const_match_instrs)
            match_instrs.append(out_block)
            match_instrs.append(Return(out_var))

    vars_seen = set()
    match_instrs = []
    const_match_instrs = []
    expr_to_ir(
        lhs,
        node_var,
        match_instrs,
        const_match_instrs,
        vars_seen,
        in_loop=False,
        last=True,
    )
    ir = CFGSeq(match_instrs)
    return ir


def gen_rule(rule):
    print(f"Compiling {rule.name}")
    node_var = Var("__node", rule.lhs.sort)
    out_var = Var("__ret", Sort(rule.rhs.sort.base, rule.rhs.sort.children))

    cfg = {}
    entry = rule_to_out_expr(cfg, None, out_var, rule.rhs)
    match_block = rule_to_match_ir(cfg, entry, node_var, out_var, rule.lhs)

    print("-------------------------------------")
    print(match_block)
    print("-------------------------------------")

    # optimize_cfg(out_var, match_block, cfg)
    # ir = in_ir + [rule.cond] + out_ir
    # opt_ir = optimize_ir(out_var, ir)

    var_counts = defaultdict(int)
    var_counts["__ret"] = 2
    cfg_count_vars(var_counts, match_block)
    match_block = cfg_optimize(out_var, var_counts, match_block)
    # cfg = cfg_optimize(var_counts, cfg)

    cfg_vars = cfg_collect_vars(match_block)
    var_decls = ""
    for var in cfg_vars:
        if var != node_var:
            var_decls += "{} {};\n".format(sort_to_code(var.sort), var.name)

    body = cfg_to_code(name_to_enum(rule.name), match_block, cfg)

    result = f"""
    inline RewriteResponse {rule.name}(TNode __node) {{
      NodeManager* nm = NodeManager::currentNM();
      {var_decls}
      {body}
    }}"""
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
    params_str = " ".join(["_"] * len(params))

    return rule_printer_pattern.format(
        name_to_enum(rule.name), name_to_enum(rule.name).lower(), params_str
    )


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
        printer_pattern.format("\n".join(gen_rule_printer(rule) for rule in rules))
    )


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
        enum_pattern.format(",".join(name_to_enum(rule.name) for rule in rules))
    )


def gen_rules_implementation(rules):
    file_pattern = """
    #ifndef CVC4__THEORY__REWRITER_RULES_IMPLEMENTATION_H
    #define CVC4__THEORY__REWRITER_RULES_IMPLEMENTATION_H

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
    }}

    #endif"""

    rules_code = []
    for rule in rules:
        rules_code.append(gen_rule(rule))

    return format_cpp(file_pattern.format("\n".join(rules_code)))


def format_cpp(s):
    p = Popen(["clang-format"], stdout=PIPE, stdin=PIPE, stderr=STDOUT)
    out = p.communicate(input=s.encode())[0]
    return out.decode()


def sort_to_lfsc(sort):
    if sort and sort.base == BaseSort.Bool:
        return "formula"
    else:  # if sort.base == BaseSort.BitVec:
        return "(term (BitVec n))"


def expr_to_lfsc(expr):
    if isinstance(expr, Fn):
        if expr.op in [Op.ZERO_EXTEND]:
            args = [expr_to_lfsc(arg) for arg in expr.children]
            return "({} zebv {} _ {})".format(
                op_to_lfsc[expr.op],
                " ".join(args[: op_to_nindex[expr.op]]),
                " ".join(args[op_to_nindex[expr.op] :]),
            )
        else:
            args = [expr_to_lfsc(arg) for arg in expr.children]
            return "({} _ {})".format(op_to_lfsc[expr.op], " ".join(args))

    elif isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, BVConst):
        return "(a_bv _ {})".format("bv{}_{}".format(expr.val, expr.bw))
    elif isinstance(expr, BoolConst):
        return "true" if expr.val else "false"


def rule_to_lfsc(rule):
    rule_pattern = """
    (declare {}
    {}
      (! u (th_holds {})
        (th_holds {}))){}"""
    closing_parens = ""

    rule_name = name_to_enum(rule.name).lower()

    params = collect_params(rule)

    varargs = []

    for param in params:
        sort_str = ""
        if param.sort.base == BaseSort.Int:
            sort_str = "mpz"
        elif param.sort.base == BaseSort.BitVec:
            sort_str = "bv"
        else:
            print("Unsupported sort: {}".format(param.sort_base))
            assert False
        varargs.append("(! {} {}".format(param.name, sort_str))
        closing_parens += ")"

    varargs.append("(! original {}".format(sort_to_lfsc(rule.lhs.sort)))
    closing_parens += ")"

    for name, sort in rule.rvars.items():
        varargs.append("(! {} {}".format(name, sort_to_lfsc(sort)))
        closing_parens += ")"

    if rule.lhs.sort.base == BaseSort.Bool:
        lhs = "(iff original {})".format(expr_to_lfsc(rule.lhs))
        rhs = "(iff original {})".format(expr_to_lfsc(rule.rhs))
    else:
        lhs = "(= _ original {})".format(expr_to_lfsc(rule.lhs))
        rhs = "(= _ original {})".format(expr_to_lfsc(rule.rhs))

    print(rule_pattern.format(rule_name, "\n".join(varargs), lhs, rhs, closing_parens))


def type_check(rules):
    for rule in rules:
        print(f"Type checking {rule.name}")
        infer_int_bounds(rule.rvars, rule.lhs)
        infer_types(rule.rvars, rule.lhs)
        assign_names(rule.lhs)
        infer_types(rule.rvars, rule.rhs)
        assign_names(rule.rhs)

        # Ensure that we were able to compute the types for both sides
        assert isinstance(rule.lhs.sort, Sort) and isinstance(rule.rhs.sort, Sort)


def compile(args):
    rules = parse_rules(args.infile.read())
    type_check(rules)
    args.rulesfile.write(gen_enum(rules))
    args.implementationfile.write(gen_rules_implementation(rules))


def dump_ir(args):
    rules = parse_rules(args.infile.read())
    rules = [rule for rule in rules if rule.name == args.rewrite]
    type_check(rules)
    print(gen_rules_implementation(rules))


def main():
    parser = argparse.ArgumentParser(description="Compile rewrite rules.")
    subparsers = parser.add_subparsers()

    parser_compile = subparsers.add_parser("compile")
    parser_compile.add_argument("infile", type=argparse.FileType("r"), help="Rule file")
    parser_compile.add_argument(
        "rulesfile", type=argparse.FileType("w"), help="File that lists the rules"
    )
    parser_compile.add_argument(
        "implementationfile",
        type=argparse.FileType("w"),
        help="File that implements the rules",
    )
    parser_compile.set_defaults(func=compile)

    parser_dump_ir = subparsers.add_parser("dump_ir")
    parser_dump_ir.add_argument("infile", type=argparse.FileType("r"), help="Rule file")
    parser_dump_ir.add_argument("rewrite", help="Name of the rewrite to dump")
    parser_dump_ir.set_defaults(func=dump_ir)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
