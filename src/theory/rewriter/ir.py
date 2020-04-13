from collections import defaultdict

from node import collect_vars, count_vars, subst, BoolConst, Var

class CFGEdge:
    def __init__(self, cond, target):
        self.cond = cond
        self.target = target

    def __repr__(self):
        return '{} -> {}'.format(self.cond, self.target)

class CFGNode:
    def __init__(self, instrs, edges):
        self.instrs = instrs
        self.edges = edges

    def __repr__(self):
        result = ''
        for instr in self.instrs:
            result += '{}\n'.format(instr)

        for edge in self.edges:
            result += str(edge) + '\n'

        return result

class IRNode:
    def __init__(self):
        pass

class Assign(IRNode):
    def __init__(self, name, expr):
        super(IRNode, self).__init__()
        assert isinstance(name, Var)
        self.name = name
        self.expr = expr

    def __repr__(self):
        return '{} := {}'.format(self.name, self.expr)

class Assert(IRNode):
    def __init__(self, expr):
        super(IRNode, self).__init__()
        self.expr = expr

    def __repr__(self):
        return 'assert {}'.format(self.expr)


def optimize_ir(out_var, instrs):
    used_vars = set([out_var])
    for instr in instrs:
        if isinstance(instr, Assert):
            used_vars |= collect_vars(instr.expr)
        elif isinstance(instr, Assign):
            used_vars |= collect_vars(instr.expr)

    opt_instrs = []
    for instr in instrs:
        if not(isinstance(instr, Assign)) or instr.name in used_vars:
            opt_instrs.append(instr)
    return opt_instrs


def optimize_cfg(out_var, entry, cfg):
    # Merge basic blocks
    change = True
    while change:
        change = False
        for label, node in cfg.items():
            if len(node.edges) == 1:
                assert node.edges[0].cond == BoolConst(True)
                next_block = cfg[node.edges[0].target]
                cfg[label].instrs += next_block.instrs
                cfg[label].edges = next_block.edges

    # Remove unused blocks
    not_called = set(cfg.keys())
    to_visit = [entry]
    while to_visit:
        curr = to_visit[-1]
        to_visit.pop()

        not_called.remove(curr)
        for edge in cfg[curr].edges:
            to_visit.append(edge.target)

    for target in not_called:
        del cfg[target]

    # Inline assignments that are used only once
    used_count = defaultdict(lambda: 0)
    substs = dict()
    for label, node in cfg.items():
        for instr in node.instrs:
            if isinstance(instr, Assert):
                count_vars(used_count, instr.expr)
            elif isinstance(instr, Assign):
                count_vars(used_count, instr.expr)
                substs[instr.name] = instr.expr

    del substs[out_var]

    # Only keep the substitutions for variables that are unused or appear once
    substs = dict(filter(lambda kv: used_count[kv[0]] <= 1, substs.items()))
    
    # Apply substitutions to themselves
    # Note: since each substituted variable can appear at most once, each
    # substitution cannot be applied more than once, so it should be enough to
    # do this n times where n is the number of substitutions
    for i in range(len(substs)):
        substs = {name:subst(expr, substs) for name, expr in substs.items()}

    # Remove unused instructions and apply substitutions
    for label, node in cfg.items():
        node.instrs = list(filter(lambda instr: (not isinstance(instr, Assign)) or (instr.name not in substs), node.instrs))
        for instr in node.instrs:
            instr.expr = subst(instr.expr, substs)

        for edge in node.edges:
            edge.cond = subst(edge.cond, substs)

def cfg_collect_vars(cfg):
    cfg_vars = set()
    for label, node in cfg.items():
        for instr in node.instrs:
            if isinstance(instr, Assign):
                cfg_vars.add(instr.name)
    return cfg_vars

def cfg_to_str(cfg):
    result = ''
    for label, node in cfg.items():
        result += '{}:\n'.format(label)
        result += str(node)
        result += '\n'
    return result
