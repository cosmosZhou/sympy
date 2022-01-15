from util import *


@apply
def apply(self):
    assert self.is_Add
    from axiom.algebra.add.to.sum import piece_together
    return Equal(self, piece_together(Integral, self))


@prove(proved=False)
def prove(Eq):
    from axiom import calculus

    x, a, b = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Integral[x:a:b](f(x)) + Integral[x:a:b](g(x)))

    return
    Eq << Eq[0].this.rhs.apply(calculus.integral.to.add)


if __name__ == '__main__':
    run()

from . import connect
# created on 2020-06-06
