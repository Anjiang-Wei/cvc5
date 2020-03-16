from enum import Enum, auto


class Op(Enum):
    BVSGT = auto()
    BVSLT = auto()
    BVULT = auto()
    BVULE = auto()
    BVNEG = auto()
    ZERO_EXTEND = auto()
    NOT = auto()

    EQ = auto()

    GET_KIND = auto()
    GET_CHILD = auto()
    MK_NODE = auto()
    MK_CONST = auto()
    BV_SIZE = auto()


class BaseSort(Enum):
    Bool = auto()
    BitVec = auto()
    Int = auto()
    Kind = auto()


class Node:
    def __init__(self, children, sort=None):
        self.children = children
        self.sort = sort


class Var(Node):
    def __init__(self, name, sort=None):
        super().__init__([], sort)
        self.name = name


class BoolConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val


class BVConst(Node):
    def __init__(self, val, bw):
        super().__init__([], Sort(BaseSort.BitVec, [bw]))
        self.val = val
        self.bw = bw


class KindConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val


class IntConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val


class GetChild(Node):
    def __init__(self, path):
        super().__init__([])
        self.path = path


class Fn(Node):
    def __init__(self, op, args):
        super().__init__(args)
        self.op = op


class Sort:
    def __init__(self, base, args):
        self.base = base
        self.args = args


def collect_vars(node):
    if isinstance(node, Var):
        return set(node.name)

    result = set()
    for child in node.children:
        result |= collect_vars(child)

    if isinstance(node, BVConst):
        result |= collect_vars(node.bw)

    return result


def unify_types(t1, t2):
    assert t1.base == t2.base
    if t1.base == BaseSort.BitVec:
        if isinstance(t1.args[0], Var) and isinstance(t2.args[0], Var):
            if t1.args[0].name == t2.args[0].name:
                return t1


def infer_types(rvars, node):
    if node.sort:
        return

    if isinstance(node, Var):
        node.sort = rvars[node.name]
        return

    for child in node.children:
        infer_types(rvars, child)

    sort = None
    if isinstance(node, Fn):
        if node.op in [Op.EQ, Op.BVSGT, Op.BVSLT, Op.BVULT]:
            sort = unify_types(node.children[0].sort, node.children[1].sort)

    node.sort = sort
