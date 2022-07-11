from util import *


@apply
def apply(self, simplify=True):
    if isinstance(self.expr, Mul):
        coefficient = []
        factors = []
        variables = self.variables
        for arg in self.expr.args:
            if not arg.has(*variables):
                coefficient.append(arg)
            elif arg.is_Pow and arg.exp.is_Add and any(not exp.has(*variables) for exp in arg.exp.args):
                base = arg.base
                for exp in arg.exp.args:
                    if exp.has(*variables):
                        factors.append(base ** exp)
                    else:
                        coefficient.append(base ** exp)
            else:
                factors.append(arg)

        if coefficient:
            return Equal(self, Mul(*coefficient, self.func(Mul(*factors), *self.limits)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)

    C = Symbol(etype=dtype.integer, given=True)

    f, h = Function(real=True)

    Eq << apply(Sum[i:C](f(i) * h(j)))

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

if __name__ == '__main__':
    run()
# created on 2018-02-15
from . import arithmetic_progression
