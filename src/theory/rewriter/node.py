from enum import Enum, auto

name_id = 0

def fresh_name(prefix):
    global name_id
    name_id += 1
    return prefix + str(name_id)

class Op(Enum):

    ###########################################################################
    # Bit-vectors
    ###########################################################################

    # Bit-vector predicates
    BVUGT = auto()
    BVUGE = auto()
    BVSGT = auto()
    BVSGE = auto()
    BVSLT = auto()
    BVSLE = auto()
    BVULT = auto()
    BVULE = auto()
    BVREDAND = auto()
    BVREDOR = auto()

    # Bit-vector arithmetic
    BVNEG = auto()
    BVADD = auto()
    BVSUB = auto()
    BVMUL = auto()
    BVSDIV = auto()
    BVUDIV = auto()
    BVSREM = auto()
    BVUREM = auto()
    BVSMOD = auto()

    # Bit-vector shifts
    BVSHL = auto()
    BVLSHR = auto()
    BVASHR = auto()
    ROTATE_LEFT = auto()
    ROTATE_RIGHT = auto()

    # Bitwise bit-vector operations
    BVNOT = auto()
    BVAND = auto()
    BVOR = auto()
    BVXOR = auto()
    BVNAND = auto()
    BVNOR = auto()
    BVXNOR = auto()

    CONCAT = auto()

    BVITE = auto()
    BVCOMP = auto()

    BVCONST = auto()
    ZERO_EXTEND = auto()
    SIGN_EXTEND = auto()
    EXTRACT = auto()
    REPEAT = auto()

    ###########################################################################
    # Boolean
    ###########################################################################

    NOT = auto()
    AND = auto()
    OR = auto()
    XOR = auto()

    ###########################################################################
    # Arithmetic
    ###########################################################################

    PLUS = auto()
    MINUS = auto()
    MULT = auto()
    LT = auto()
    GEQ = auto()

    ###########################################################################
    # Theory-independent
    ###########################################################################

    EQ = auto()
    ITE = auto()

    ###########################################################################
    # Node manipulation
    ###########################################################################

    GET_KIND = auto()
    GET_CHILD = auto()
    GET_CHILDREN = auto()
    GET_INDEX = auto()
    GET_CONST = auto()
    MK_NODE = auto()
    MK_CONST = auto()
    IS_NULL = auto()
    BV_SIZE = auto()
    APPEND = auto()
    POW2 = auto()
    BITS = auto()

    ###########################################################################
    # Language operators
    ###########################################################################

    # Conditional
    COND = auto()
    # Case in a conditional
    CASE = auto()
    # Let binding
    LET = auto()
    FAIL = auto()
    MAP = auto()
    LAMBDA = auto()
    APPLY = auto()

fns = set(["pow2"])
commutative_ops = set([Op.BVADD, Op.BVMUL, Op.BVAND, Op.BVOR, Op.BVXOR, Op.AND, Op.OR, Op.XOR, Op.EQ])
associative_ops = set([Op.BVADD, Op.BVMUL, Op.BVAND, Op.BVOR, Op.BVXOR, Op.CONCAT, Op.AND, Op.OR, Op.XOR, Op.EQ])
nary_ops = set([Op.BVADD, Op.BVMUL, Op.BVAND, Op.BVOR, Op.BVXOR, Op.CONCAT, Op.AND, Op.OR])


class BaseSort(Enum):
    Bool = auto()
    BitVec = auto()
    Int = auto()
    Kind = auto()
    List = auto()
    Fail = auto()


class Node:
    def __init__(self, children, sort=None):
        assert all(isinstance(child, Node) for child in children)
        self.children = children
        self.sort = sort
        self.name = None

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
        print(self.name)
        print(self.name.__class__)
        print(other)
        print(other.__class__)
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def __repr__(self):
        return self.name


class IntConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)


class BoolConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __repr__(self):
        return str(self.val)


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

    def __repr__(self):
        return str(self.val)


class IntConst(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __repr__(self):
        return str(self.val)


class Fn(Node):
    def __init__(self, op, args):
        super().__init__(args)
        self.op = op

    def __eq__(self, other):
        return isinstance(other,
                          Fn) and self.op == other.op and super().__eq__(other)

    def __hash__(self):
        return hash((self.op, tuple(self.children)))

    def __repr__(self):
        return '({} {})'.format(
            self.op, ' '.join(str(child) for child in self.children))


class Sort(Node):
    def __init__(self, base, args, const=False):
        super().__init__(args)
        self.base = base
        self.const = const

    def __eq__(self, other):
        return self.base == other.base and super().__eq__(other)

    def __hash__(self):
        return hash((self.base, tupe(self.children)))

    def __repr__(self):
        return '({} {}{})'.format(
            self.base, ' '.join(str(child) for child in self.children),
            ' :const' if self.const else '')


def collect_vars(node):
    if isinstance(node, Var):
        return set(node.name)

    result = set()
    for child in node.children:
        result |= collect_vars(child)

    if isinstance(node, BVConst):
        result |= collect_vars(node.bw)

    return result


def count_vars(counts, node):
    if isinstance(node, Var):
        counts[node] += 1
    else:
        for child in node.children:
            count_vars(counts, child)


def subst(node, substs):
    # TODO: non-destructive substitution?
    if node in substs:
        return substs[node]
    else:
        new_children = []
        for child in node.children:
            new_children.append(subst(child, substs))
        node.children = new_children
        return node


def unify_types(t1, t2):
    assert t1.base == t2.base
    if t1.base == BaseSort.BitVec:
        if isinstance(t1.args[0], Var) and isinstance(t2.args[0], Var):
            if t1.args[0].name == t2.args[0].name:
                return t1


def are_types_compatible(t1, t2):
    if t1.base == t2.base:
        return True
    if t1.base == BaseSort.List:
        return are_types_compatible(t1.children[0], t2)
    elif t2.base == BaseSort.List:
        return are_types_compatible(t1, t2.children[0])
    return False


def infer_types(context, node):
    if node.sort:
        # Sort has already been computed for this node, skip
        return

    if isinstance(node, Var):
        # Variable sorts are declared in the context
        node.sort = context[node.name]
        return

    if isinstance(node, Fn):
        if node.op == Op.LET:
            infer_types(context, node.children[1])
            node.children[0].sort = node.children[1].sort
            child_context = context.copy()
            child_context[node.children[0].name] = node.children[1].sort
            infer_types(child_context, node.children[2])
            node.sort = node.children[2].sort
            return
        elif node.op == Op.LAMBDA:
            infer_types(context, node.children[0])
            child_context = context.copy()
            child_context[node.children[0].name] = node.children[0].sort
            infer_types(child_context, node.children[1])
            node.sort = node.children[1].sort
            return

    for child in node.children:
        infer_types(context, child)

    sort = None
    if isinstance(node, Fn):
        if node.op in [
                Op.BVUGT, Op.BVUGE, Op.BVSGT, Op.BVSGE, Op.BVSLT, Op.BVSLE,
                Op.BVULT, Op.BVULE
        ]:
            assert node.children[0].sort.base == BaseSort.BitVec
            assert node.children[0].sort == node.children[1].sort
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [Op.BVREDAND, Op.BVREDOR]:
            assert node.children[0].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [
                Op.BVADD, Op.BVSUB, Op.BVMUL, Op.BVSDIV, Op.BVUDIV, Op.BVSREM, Op.BVUREM,
                Op.BVSMOD, Op.BVSHL, Op.BVLSHR, Op.BVASHR, Op.BVAND, Op.BVOR,
                Op.BVXOR, Op.BVNAND, Op.BVNOR, Op.BVXNOR
        ]:
            assert node.children[0].sort.base == BaseSort.BitVec or (
                node.children[0].sort.base == BaseSort.List
                and node.children[0].sort.children[0].base == BaseSort.BitVec)
            arg_sort = node.children[0].sort
            assert all(
                are_types_compatible(arg_sort, child.sort)
                for child in node.children)
            sort = Sort(BaseSort.BitVec, [node.children[0].sort.children[0]])
        elif node.op in [Op.ROTATE_LEFT, Op.ROTATE_RIGHT]:
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.BitVec
            sort = node.children[1].sort
        elif node.op in [Op.CONCAT]:
            assert node.children[0].sort.base == BaseSort.BitVec or (
                node.children[0].sort.base == BaseSort.List
                and node.children[0].sort.children[0].base == BaseSort.BitVec)
            arg_sort = node.children[0].sort
            assert all(
                are_types_compatible(arg_sort, child.sort)
                for child in node.children)
            sort = Sort(BaseSort.BitVec, [
                Fn(Op.PLUS, [
                    child.sort.children[0] for child in node.children
                ])
            ])
        elif node.op in [Op.ZERO_EXTEND, Op.SIGN_EXTEND]:
            assert len(node.children) == 2
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [
                Fn(Op.PLUS,
                   [node.children[0], node.children[1].sort.children[0]])
            ])
        elif node.op == Op.REPEAT:
            assert len(node.children) == 2
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [
                Fn(Op.MULT,
                   [node.children[0], node.children[1].sort.children[0]])
            ])
        elif node.op in [Op.EXTRACT]:
            assert len(node.children) == 3
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.Int
            assert node.children[2].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [
                Fn(Op.PLUS, [
                    Fn(Op.MINUS, [node.children[0], node.children[1]]),
                    IntConst(1)
                ])
            ])
        elif node.op in [Op.BVNEG, Op.BVNOT]:
            assert node.children[0].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [node.children[0].sort.children[0]])
        elif node.op == Op.BVITE:
            # TODO: check bit-width of condition
            # TODO: check that the types are the same across branches
            assert node.children[0].sort.base == BaseSort.BitVec
            assert node.children[1].sort.base == BaseSort.BitVec
            assert node.children[2].sort.base == BaseSort.BitVec
            sort = node.children[1].sort
        elif node.op == Op.BVCOMP:
            # TODO: check that the types are the same across branches
            assert node.children[0].sort.base == BaseSort.BitVec
            assert node.children[1].sort.base == BaseSort.BitVec
            sort = Sort(BaseSort.BitVec, [IntConst(1)])
        elif node.op in [Op.NOT]:
            assert node.children[0].sort.base == BaseSort.Bool
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [Op.EQ]:
            assert node.children[0].sort.base == node.children[1].sort.base
            sort = Sort(BaseSort.Bool, [])
        elif node.op == Op.ITE:
            # TODO: check that the types are the same across branches
            assert node.children[0].sort.base == BaseSort.Bool
            assert node.children[1].sort.base == node.children[2].sort.base
            sort = node.children[1].sort
        elif node.op in [Op.CASE]:
            assert node.children[0].sort == Sort(BaseSort.Bool, [])
            sort = Sort(node.children[1].sort.base,
                        node.children[1].sort.children[:])
        elif node.op in [Op.COND]:
            # TODO: check that types are the same across branches
            sort = Sort(node.children[0].sort.base,
                        node.children[0].sort.children[:])
        elif node.op in [Op.BVCONST]:
            sort = Sort(BaseSort.BitVec, [node.children[1]])
        elif node.op in [Op.PLUS, Op.MINUS]:
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.Int
            sort = Sort(BaseSort.Int, [])
        elif node.op in [Op.LT, Op.GEQ]:
            assert node.children[0].sort.base == BaseSort.Int
            assert node.children[1].sort.base == BaseSort.Int
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [Op.XOR]:
            assert node.children[0].sort.base == BaseSort.Bool
            assert node.children[1].sort.base == BaseSort.Bool
            sort = Sort(BaseSort.Bool, [])
        elif node.op in [Op.BITS]:
            sort = Sort(BaseSort.Int, [], True)
        elif node.op in [Op.POW2]:
            sort = Sort(BaseSort.Int, [], True)
        elif node.op in [Op.AND, Op.OR]:
            assert all(child.sort.base == BaseSort.Bool or (
                child.sort.base == BaseSort.List
                and child.sort.children[0].base == BaseSort.Bool)
                       for child in node.children)
            # TODO: Check that list is used correctly
            sort = Sort(BaseSort.Bool, [])
        elif node.op == Op.FAIL:
            sort = Sort(BaseSort.Fail, [], True)
        elif node.op == Op.MAP:
            assert node.children[1].sort.base == BaseSort.List
            sort = Sort(BaseSort.List, [node.children[0].sort], True)
        else:
            print('Unsupported operator: {}'.format(node.op))
            assert False

        sort.const = all(child.sort.const for child in node.children)
    elif isinstance(node, IntConst):
        sort = Sort(BaseSort.Int, [])
        sort.const = True
    elif isinstance(node, BoolConst):
        sort = Sort(BaseSort.Bool, [])
        sort.const = True

    node.sort = sort


def assign_names(node):
    if node.name:
        return

    node.name = fresh_name('node')
    for child in node.children:
        assign_names(child)
