from node import collect_vars, BoolConst

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


def optimize_cfg(entry, cfg):
    change = True
    while change:
        change = False
        for label, node in cfg.items():
            if len(node.edges) == 1:
                assert node.edges[0].cond == BoolConst(True)
                next_block = cfg[node.edges[0].target]
                cfg[label].instrs += next_block.instrs
                cfg[label].edges = next_block.edges

    not_called = set(cfg.keys())
    not_called.remove(entry)
    for label, node in cfg.items():
        for edge in node.edges:
            if edge.target in not_called:
                not_called.remove(edge.target)

    for target in not_called:
        del cfg[target]

def cfg_to_str(cfg):
    result = ''
    for label, node in cfg.items():
        result += '{}:\n'.format(label)
        result += str(node)
        result += '\n'
    return result
