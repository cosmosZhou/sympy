from util import *


@apply
def apply(self):
    n, d = self.of(Ceiling[Expr / Expr])
    return Equal(self, (n + d - 1) // d)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(ceiling(n / d))

    Eq << Eq[-1].this.lhs.apply(algebra.ceiling.to.mul)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] + (-n // d - 1)

    Eq << Eq[-1].reversed

    Eq << algebra.mod.to.add.apply(-n % d)

    Eq << algebra.mod.to.add.apply((d + n - 1) % d)

    Eq << Eq[-1] + Eq[-2] - (d - 1)

    Eq << Eq[-1] / d

    Eq << Eq[-1].this.rhs.ratsimp()

    Eq << Eq[-1] - 1


if __name__ == '__main__':
    run()
# created on 2018-05-25
