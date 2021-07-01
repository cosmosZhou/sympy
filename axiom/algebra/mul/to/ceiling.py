from util import *


@apply
def apply(self):
    x = self.of(-Floor)
    return Equal(self, ceiling(-x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    Eq << apply(-floor(x))

    Eq << Eq[0].this.rhs.apply(algebra.ceiling.to.mul)


if __name__ == '__main__':
    run()
