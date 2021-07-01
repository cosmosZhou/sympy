from util import *


@apply
def apply(self):
    x = self.of(Ceiling)

    return Equal(self, frac(-x) + x)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    Eq << apply(ceiling(x))

    Eq << Eq[0].this.rhs.args[1].apply(algebra.frac.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)


if __name__ == '__main__':
    run()
