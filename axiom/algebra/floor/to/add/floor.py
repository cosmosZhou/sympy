from util import *


@apply
def apply(self):
    x = self.of(Floor)
    x = 2 * x + 1
    assert x.is_integer

    return Equal(self, x - x // 2 - 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(integer=True)
    Eq << apply((x - 1) // 2)

    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.ceiling)

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.add.frac)

    Eq << Eq[-1] - x / 2

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.frac)

    Eq << Eq[-1].this.lhs.apply(algebra.frac.half)


if __name__ == '__main__':
    run()

# created on 2019-05-11
# updated on 2019-05-11
