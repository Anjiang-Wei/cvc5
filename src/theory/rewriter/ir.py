from collections import defaultdict

from node import collect_vars, count_vars, subst, BoolConst, Var, Node, Fn


class CFGEdge:
    def __init__(self, cond, target):
        self.cond = cond
        self.target = target

    def __repr__(self):
        return '{} -> {}'.format(self.cond, self.target)


class BaseNode:
    pass

class CFGSeq(BaseNode):
    def __init__(self, instrs):
        self.instrs = instrs

    def __repr__(self):
        result = ''
        for instr in self.instrs:
            result += '{}\n'.format(instr)
        return result

class CFGCond(BaseNode):
    def __init__(self, cases):
        self.cases = cases

    def __repr__(self):
        result = ''
        for case in self.cases:
            result += f'{case[0]} => {case[1]}\n'
        return result

class CFGNode(BaseNode):
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


class CFGLoop(BaseNode):
    def __init__(self, loop_var, domain, body):
        assert isinstance(loop_var, Var)
        self.loop_var = loop_var
        self.domain = domain
        self.body = body

    def __repr__(self):
        result = 'for {} in {}:\n'.format(self.loop_var, self.domain)
        result += str(self.body)
        result += 'end'
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
    def __init__(self, expr, in_loop):
        super(IRNode, self).__init__()
        self.expr = expr
        self.in_loop = in_loop

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
        if not (isinstance(instr, Assign)) or instr.name in used_vars:
            opt_instrs.append(instr)
    return opt_instrs


def optimize_cfg(out_var, entry, cfg):
    # Merge basic blocks
    change = True
    while change:
        change = False
        for label, node in cfg.items():
            if isinstance(node, CFGNode) and len(node.edges) == 1 and isinstance(node.edges[0], CFGNode):
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
        if isinstance(cfg[curr], CFGNode):
            for edge in cfg[curr].edges:
                to_visit.append(edge.target)
        elif isinstance(cfg[curr], CFGLoop):
            to_visit.append(cfg[curr].body)

    for target in not_called:
        del cfg[target]

    return

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

        for edge in node.edges:
            count_vars(used_count, edge.cond)

    del substs[out_var]

    # Only keep the substitutions for variables that are unused or appear once
    substs = dict(filter(lambda kv: used_count[kv[0]] <= 1, substs.items()))

    # Apply substitutions to themselves
    # Note: since each substituted variable can appear at most once, each
    # substitution cannot be applied more than once, so it should be enough to
    # do this n times where n is the number of substitutions
    for i in range(len(substs)):
        substs = {name: subst(expr, substs) for name, expr in substs.items()}

    # Remove unused instructions and apply substitutions
    for label, node in cfg.items():
        node.instrs = list(
            filter(
                lambda instr:
                (not isinstance(instr, Assign)) or (instr.name not in substs),
                node.instrs))
        for instr in node.instrs:
            instr.expr = subst(instr.expr, substs)

        for edge in node.edges:
            edge.cond = subst(edge.cond, substs)


def cfg_collect_vars(node):
    cfg_vars = set()
    if isinstance(node, CFGLoop):
        cfg_vars.add(node.loop_var)
        cfg_vars.update(cfg_collect_vars(node.domain))
        cfg_vars.update(cfg_collect_vars(node.body))
    elif isinstance(node, CFGSeq) or isinstance(node, CFGNode):
        for instr in node.instrs:
            cfg_vars.update(cfg_collect_vars(instr))
    elif isinstance(node, CFGCond):
        for case in node.cases:
            cfg_vars.update(cfg_collect_vars(case[0]))
            cfg_vars.update(cfg_collect_vars(case[1]))
    elif isinstance(node, Assign):
        cfg_vars.add(node.name)
        cfg_vars.update(cfg_collect_vars(node.expr))
    return cfg_vars

def cfg_count_vars(var_counts, node):
    if isinstance(node, CFGLoop):
        var_counts[node.loop_var.name] += 1
    elif isinstance(node, CFGSeq) or isinstance(node, CFGNode):
        for instr in node.instrs:
            cfg_count_vars(var_counts, instr)
    elif isinstance(node, CFGCond):
        for case in node.cases:
            cfg_count_vars(var_counts, case[0])
            cfg_count_vars(var_counts, case[1])
    elif isinstance(node, Assign):
        cfg_count_vars(var_counts, node.expr)
    elif isinstance(node, Assert):
        cfg_count_vars(var_counts, node.expr)
    elif isinstance(node, Node):
        if isinstance(node, Var):
            var_counts[node.name] += 1
        else:
            for child in node.children:
                cfg_count_vars(var_counts, child)

def cfg_optimize(var_counts, node):
    def remove_unused_vars(node):
        if isinstance(node, CFGLoop):
            node
        elif isinstance(node, CFGSeq) or isinstance(node, CFGNode):
            new_instrs = []
            for instr in node.instrs:
                new_instr = remove_unused_vars(instr)
                if new_instr:
                    new_instrs.append(new_instr)
            return CFGSeq(new_instrs)
        elif isinstance(node, CFGCond):
            new_cases = []
            for case in node.cases:
                new_cases.append((remove_unused_vars(case[0]), remove_unused_vars(case[1])))
            return CFGCond(new_cases)
        elif isinstance(node, Assign):
            res = None if node.name.name not in var_counts else node
            return res
        else:
            return node

    substs = dict()
    def elim_single_use_vars(node):
        if isinstance(node, CFGLoop):
            node
        elif isinstance(node, CFGSeq) or isinstance(node, CFGNode):
            new_instrs = []
            for instr in node.instrs:
                new_instr = elim_single_use_vars(instr)
                if new_instr:
                    new_instrs.append(new_instr)
            return CFGSeq(new_instrs)
        elif isinstance(node, CFGCond):
            new_cases = []
            for case in node.cases:
                new_cases.append((elim_single_use_vars(case[0]), elim_single_use_vars(case[1])))
            return CFGCond(new_cases)
        elif isinstance(node, Assign):
            res = None
            new_expr = elim_single_use_vars(node.expr)
            if var_counts[node.name.name] == 1:
                substs[node.name.name] = new_expr
            else:
                res = Assign(node.name, new_expr)
            return res
        elif isinstance(node, Assert):
            return Assert(elim_single_use_vars(node.expr), node.in_loop)
        elif isinstance(node, Node):
            if isinstance(node, Var) and node.name in substs:
                return substs[node.name]
            elif isinstance(node, Fn):
                new_children = []
                for child in node.children:
                    new_children.append(elim_single_use_vars(child))
                new_node = Fn(node.op, new_children)
                new_node.sort = node.sort
                return new_node
            else:
                return node
        else:
            return node

    return elim_single_use_vars(remove_unused_vars(node))

def cfg_to_str(cfg):
    result = ''
    for label, node in cfg.items():
        result += '{}:\n'.format(label)
        result += str(node)
        result += '\n'
    return result
