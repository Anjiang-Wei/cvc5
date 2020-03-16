from node import collect_vars

class IRNode:
    def __init__(self):
        pass


class Assign(IRNode):
    def __init__(self, name, expr):
        super(IRNode, self).__init__()
        self.name = name
        self.expr = expr


class Assert(IRNode):
    def __init__(self, expr):
        super(IRNode, self).__init__()
        self.expr = expr


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
