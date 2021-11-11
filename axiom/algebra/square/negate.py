from util import *


@apply
def apply(self):
    args = self.of(Add ** 2)

    return Equal(self, Add(*(-arg for arg in args)) ** 2)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply((x - y) ** 2)

    Eq << Eq[-1].this.lhs.apply(algebra.square.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.square.to.add)


if __name__ == '__main__':
    run()
# created on 2019-11-07
# updated on 2019-11-07
