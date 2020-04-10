from enum import Enum, auto


class Op(Enum):
    BVUGT = auto()
    BVUGE = auto()
    BVSGT = auto()
    BVSGE = auto()
    BVSLT = auto()
    BVSLE = auto()
    BVULT = auto()
    BVULE = auto()

    BVNEG = auto()
    BVADD = auto()
    BVSUB = auto()

    CONCAT = auto()

    ZERO_EXTEND = auto()

    PLUS = auto()

    NOT = auto()

    EQ = auto()

    GET_KIND = auto()
    GET_CHILD = auto()
    GET_INDEX = auto()
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

    def __eq__(self, other):
        if len(self.children) != len(other.children):
            return False

        for c1, c2 in zip(self.children, other.children):
            if c1 != c2:
                return False

        return True

class Var(Node):
    def __init__(self, name, sort=None):
        super().__init__([], sort)
        self.name = name


    def __eq__(self, other):
        return self.name == other.name


    def __hash__(self):
        return hash(self.name)

    def __repr__(self):
        return self.name


class BoolConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)

class BVConst(Node):
    def __init__(self, val, bw):
        super().__init__([], Sort(BaseSort.BitVec, [bw]))
        self.val = val
        self.bw = bw

    def __eq__(self, other):
        return self.val == other.val and self.bw == other.bw

    def __hash__(self):
        return hash((self.bw, self.val))

class KindConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)

class IntConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)

class GetChild(Node):
    def __init__(self, path):
        super().__init__([])
        self.path = path

class GetIndex(Node):
    def __init__(self, path):
        super().__init__([])
        self.path = path

class Fn(Node):
    def __init__(self, op, args):
        super().__init__(args)
        self.op = op

    def __eq__(self, other):
        return self.op == other.op and super().__eq__(other)

    def __hash__(self):
        return hash((self.op, tuple(self.children)))


class Sort(Node):
    def __init__(self, base, args):
        super().__init__(args)
        self.base = base
        print(base, args)

    def __eq__(self, other):
        return self.base == other.base and super().__eq__(other)

    def __hash__(self):
        return hash((self.base, tupe(self.children)))

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
        if node.op in [
            Op.BVUGT,
            Op.BVUGE,
            Op.BVSGT,
            Op.BVSGE,
            Op.BVSLT,
            Op.BVSLE,
            Op.BVULT,
            Op.BVULE]:
            assert node.children[0].sort.base == BaseSort.BitVec
            assert node.children[0].sort == node.children[1].sort
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [
            Op.BVADD,
            Op.BVSUB]:
            assert node.children[0].sort.base == BaseSort.BitVec
            assert node.children[0].sort == node.children[1].sort
            sort = node.children[0].sort
        elif node.op in [Op.CONCAT]:
            assert node.children[0].sort.base == BaseSort.BitVec
            assert node.children[1].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [Fn(Op.PLUS, [node.children[0].sort.children[0], node.children[1].sort.children[1]])])
        elif node.op in [Op.ZERO_EXTEND]:
            assert len(node.children) == 2
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [Fn(Op.PLUS, [node.children[0], node.children[1].sort.children[0]])])
        elif node.op in [Op.BVNEG]:
            assert node.children[0].sort.base == BaseSort.BitVec
            sort = node.children[0].sort
        elif node.op in [Op.NOT]:
            assert node.children[0].sort.base == BaseSort.Bool
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [Op.EQ]:
            assert node.children[0].sort == node.children[1].sort
            sort = Sort(BaseSort.Bool, [])
        else:
            print('Unsupported operator: {}'.format(node.op))
            assert False

    node.sort = sort
    print(node.op, sort)
