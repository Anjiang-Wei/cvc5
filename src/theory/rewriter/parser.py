import pyparsing as pp

from node import *
from rule import Rule

symbol_to_op = {
    'bvugt': Op.BVUGT,
    'bvuge': Op.BVUGE,
    'bvsgt': Op.BVSGT,
    'bvsge': Op.BVSGE,
    'bvslt': Op.BVSLT,
    'bvsle': Op.BVSLE,
    'bvult': Op.BVULT,
    'bvule': Op.BVULE,
    'bvredand': Op.BVREDAND,
    'bvredor': Op.BVREDOR,
    'bvneg': Op.BVNEG,
    'bvadd': Op.BVADD,
    'bvsub': Op.BVSUB,
    'bvmul': Op.BVMUL,
    'bvsdiv': Op.BVSDIV,
    'bvudiv': Op.BVUDIV,
    'bvsrem': Op.BVSREM,
    'bvurem': Op.BVUREM,
    'bvsmod': Op.BVSMOD,
    'bvshl': Op.BVSHL,
    'bvlshr': Op.BVLSHR,
    'bvashr': Op.BVASHR,
    'rotate_left': Op.ROTATE_LEFT,
    'rotate_right': Op.ROTATE_RIGHT,
    'bvnot': Op.BVNOT,
    'bvand': Op.BVAND,
    'bvor': Op.BVOR,
    'bvxor': Op.BVXOR,
    'bvnand': Op.BVNAND,
    'bvnor': Op.BVNOR,
    'bvxnor': Op.BVXNOR,
    'concat': Op.CONCAT,
    'bvite': Op.BVITE,
    'bvcomp': Op.BVCOMP,
    'bv': Op.BVCONST,
    'zero_extend': Op.ZERO_EXTEND,
    'sign_extend': Op.SIGN_EXTEND,
    'extract': Op.EXTRACT,
    'repeat': Op.REPEAT,
    'not': Op.NOT,
    'and': Op.AND,
    'or': Op.OR,
    'xor': Op.XOR,
    '+': Op.PLUS,
    '-': Op.MINUS,
    '*': Op.MULT,
    '<': Op.LT,
    '>=': Op.GEQ,
    '<<': Op.LEFT_SHIFT,
    '=': Op.EQ,
    'ite': Op.ITE,

    'pow2': Op.POW2,
    'npow2': Op.NPOW2,
    'zeroes': Op.ZEROES,
}


def bv_to_int(s):
    assert s.startswith('bv')
    return int(s[2:])


def symbol():
    special_chars = '=' + '_' + '+' + '-' + '<' + '>' + '*'
    return pp.Word(pp.alphas + special_chars, pp.alphanums + special_chars)


def mk_let(let):
    body = let[-1]
    for binding in reversed(let[0:-1]):
        body = Fn(Op.LET, [binding[0], binding[1], body])
    return body


def mk_case(cases):
    if not isinstance(cases[-1], Fn) or cases[-1].op != Op.CASE:
        cases[-1] = Fn(Op.CASE, [BoolConst(True), cases[-1]])
    else:
        cases.append(Fn(Op.CASE, [BoolConst(True), Fn(Op.FAIL, [])]))
    return Fn(Op.COND, cases)


def expr(allow_comprehension = True):
    expr = pp.Forward()

    # Variable
    var = symbol().setParseAction(lambda s, l, t: Var(t[0]))

    # Constants
    bconst = pp.Keyword('true').setParseAction(
        lambda s, l, t: BoolConst(True)) | pp.Keyword('false').setParseAction(
            lambda s, l, t: BoolConst(False))
    iconst = pp.Word(
        pp.nums).setParseAction(lambda s, l, t: IntConst(int(t[0])))
    bvconst = (
        pp.Suppress('(') + pp.Suppress('_') + pp.Keyword('bv') + expr + expr +
        ')').setParseAction(lambda s, l, t: Fn(Op.BVCONST, [t[1], t[2]]))

    # Function applications
    indexed_app = (pp.Suppress('(') + pp.Suppress('(') + pp.Suppress('_') +
                   symbol() + pp.OneOrMore(expr) + pp.Suppress(')') +
                   pp.OneOrMore(expr) + pp.Suppress(')')).setParseAction(
                       lambda s, l, t: Fn(symbol_to_op[t[0]], t[1:]))
    app = (pp.Suppress('(') + symbol() + pp.OneOrMore(expr) + pp.Suppress(')')
           ).setParseAction(lambda s, l, t: Fn(symbol_to_op[t[0]], t[1:]))

    # Let bindings
    binding = (pp.Suppress('(') + var + expr +
               pp.Suppress(')')).setParseAction(lambda s, l, t: (t[0], t[1]))
    let = (pp.Suppress('(') + pp.Keyword('let') + pp.Suppress('(') +
           pp.OneOrMore(binding) + pp.Suppress(')') + expr +
           pp.Suppress(')')).setParseAction(lambda s, l, t: mk_let(t[1:]))

    # Conditionals
    case = (pp.Suppress('(') + expr + expr + pp.Suppress(')')
            ).setParseAction(lambda s, l, t: Fn(Op.CASE, [t[0], t[1]]))
    cond = (pp.Suppress('(') + pp.Keyword('cond') + pp.OneOrMore(case) +
            pp.Optional(expr) +
            pp.Suppress(')')).setParseAction(lambda s, l, t: mk_case(t[1:]))

    options = bconst | iconst | bvconst | cond | indexed_app | app | let | var
    if allow_comprehension:
        lambda_def = (pp.Suppress('(') + pp.Keyword('lambda') + pp.Suppress('(') + symbol() + sort() + pp.Suppress(')') + expr + pp.Suppress(')')).setParseAction(lambda s, l, t: Fn(Op.LAMBDA, [Var(t[1], t[2]), t[3]]))
        comprehension = (pp.Suppress('(') + pp.Keyword('map') + lambda_def + expr() + pp.Suppress(')')).setParseAction(lambda s, l, t: Fn(Op.MAP, [t[1], t[2]]))
        options = comprehension | options 


    expr <<= options
    return expr


def sort():
    bv_sort = (pp.Suppress('(') + (pp.Suppress('_') + pp.Keyword('BitVec')) +
               expr(False) + pp.Suppress(')')
               ).setParseAction(lambda s, l, t: Sort(BaseSort.BitVec, [t[1]]))
    int_sort = pp.Keyword('Int').setParseAction(
        lambda s, l, t: Sort(BaseSort.Int, []))
    bool_sort = pp.Keyword('Bool').setParseAction(
        lambda s, l, t: Sort(BaseSort.Bool, []))
    return bv_sort | int_sort | bool_sort


def process_var_decl(name, sort, attrs):
    if ':const' in attrs:
        sort.const = True
    elif ':list' in attrs:
        sort = Sort(BaseSort.List, [sort])
    return (name, sort)


def attrs():
    return pp.Keyword(':list') | pp.Keyword(':const')


def var_decl():
    return (pp.Suppress('(') + symbol() + sort() + pp.ZeroOrMore(attrs()) +
            pp.Suppress(')')).setParseAction(
                lambda s, l, t: process_var_decl(t[0], t[1], t[2:]))


def var_list():
    return (pp.Suppress('(') + pp.OneOrMore(var_decl()) +
            pp.Suppress(')')).setParseAction(lambda s, l, t: dict(t[:]))


def parse_rules(s):
    comments = pp.ZeroOrMore(pp.Suppress(pp.cStyleComment))

    rule = comments + (pp.Suppress('(') + pp.Keyword('define-rule') +
                       pp.Word(pp.alphas) + var_list() + expr() + expr() +
                       pp.Suppress(')')).setParseAction(lambda s, l, t: Rule(
                           t[1], t[2], BoolConst(True), t[3], t[4]))
    rules = pp.OneOrMore(rule) + comments + pp.StringEnd()
    return rules.parseString(s)
