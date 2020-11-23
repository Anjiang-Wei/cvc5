from node import *

class ProofRule:
    def __init__(name, params, arguments, subproofs):
        self.name = name
        self.params = params
        self.arguments = arguments
        self.subproofs = subproofs

def collect_node_sort_params(node):
    params = set()

    if isinstance(node, BVConst):
        v = Var('bv{}_{}'.format(node.val, node.bw))
        v.sort = Sort(BaseSort.BitVec, [node.bw])
        params.add(v) 

    if isinstance(node, Fn):
        if node.op in [Op.ZERO_EXTEND]:
            v = Var('zebv')
            v.sort = Sort(BaseSort.Int, [])
            params.add(v) 

            v = Var('zeamount')
            v.sort = Sort(BaseSort.Int, [])
            params.add(v) 

    for child in node.children:
        params |= collect_node_sort_params(child)

    if isinstance(node, Var) and node.sort.base == BaseSort.Int:
        params.add(node)

    return params

def collect_params(rule):
    params = set()
    for name, sort in rule.rvars.items():
        if sort.base == BaseSort.BitVec and isinstance(sort.children[0], Var):
            sort.children[0].sort = Sort(BaseSort.Int, [])
            params.add(sort.children[0])

    params |= collect_node_sort_params(rule.lhs)
    return params
