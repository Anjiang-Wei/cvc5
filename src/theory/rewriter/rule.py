class Rule:
    def __init__(self, name, rvars, cond, lhs, rhs):
        self.name = name
        self.rvars = rvars
        self.cond = cond
        self.lhs = lhs
        self.rhs = rhs
