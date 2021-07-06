from util import *


@apply
def apply(self):
    x = self.of(Abs)
    return Equal(self, Piecewise((-x, x <= 0), (x, True)))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    Eq << apply(abs(x))

    Eq << algebra.abs.to.piecewise.is_positive.apply(abs(x))

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.swap.front)


if __name__ == '__main__':
    run()