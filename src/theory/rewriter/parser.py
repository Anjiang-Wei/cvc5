import pyparsing as pp

from node import *
from rule import Rule

symbol_to_op = {
    'bvsgt': Op.BVSGT,
    'bvslt': Op.BVSLT,
    'bvult': Op.BVULT,
    'bvule': Op.BVULE,
    'bvneg': Op.BVNEG,
    'not': Op.NOT,
    '=': Op.EQ
}


def bv_to_int(s):
    assert s.startswith('bv')
    return int(s[2:])


def parse_expr():
    expr = pp.Forward()
    bconst = pp.Keyword('true').setParseAction(
        lambda s, l, t: BoolConst(True)) | pp.Keyword('false').setParseAction(
            lambda s, l, t: BoolConst(False))
    bvconst = (
        pp.Suppress('(') + pp.Suppress('_') + pp.Word(pp.alphanums) + expr +
        ')').setParseAction(lambda s, l, t: BVConst(bv_to_int(t[0]), t[1]))
    app = (pp.Suppress('(') + pp.Word(pp.alphas + '=') + pp.OneOrMore(expr) +
           pp.Suppress(')')
           ).setParseAction(lambda s, l, t: Fn(symbol_to_op[t[0]], t[1:]))
    expr <<= bconst | bvconst | app | pp.Word(
        pp.alphas).setParseAction(lambda s, l, t: Var(t[0]))
    return expr


def parse_sort():
    return (pp.Suppress('(') + (pp.Suppress('_') + pp.Keyword('BitVec')) +
            parse_expr() + pp.Suppress(')')
            ).setParseAction(lambda s, l, t: Sort(BaseSort.BitVec, [t[1]]))


def parse_var():
    return (pp.Suppress('(') + pp.Word(pp.alphas) + parse_sort() +
            pp.Suppress(')')).setParseAction(lambda s, l, t: (t[0], t[1]))


def parse_var_list():
    return (pp.Suppress('(') + pp.OneOrMore(parse_var()) +
            pp.Suppress(')')).setParseAction(lambda s, l, t: dict(t[:]))


def parse_rules(s):
    comments = pp.ZeroOrMore(pp.Suppress(pp.cStyleComment))

    rule = (pp.Suppress('(') + pp.Keyword('define-rule') + pp.Word(pp.alphas) +
            parse_var_list() + parse_expr() + parse_expr() +
            pp.Suppress(')')).setParseAction(
                lambda s, l, t: Rule(t[1], t[2], BoolConst(True), t[3], t[4]))
    rules = pp.OneOrMore(rule)
    return rules.parseString(s)
