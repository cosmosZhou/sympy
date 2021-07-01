from util import *


@apply
def apply(self, simplify=True):
    if isinstance(self.function, Mul):
        coefficient = []
        factors = []
        variables = self.variables
        for arg in self.function.args:
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
            return Equal(self, Mul(*coefficient, self.func(Mul(*factors), *self.limits)))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    C = Symbol.C(etype=dtype.integer, given=True)

    f = Function.f(real=True)
    h = Function.h(real=True)

    Eq << apply(Sum[i:C](f(i) * h(j)))

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

if __name__ == '__main__':
    run()
from . import st
