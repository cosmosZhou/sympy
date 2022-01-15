from util import *


@apply
def apply(self):
    n, d = self.of(Ceiling[Expr / Expr])
    return Equal(self, (n - 1) // d + 1)


@prove
def prove(Eq):
    from axiom import algebra
    n, d = Symbol(integer=True)
    Eq << apply(ceiling(n / d))

    Eq << Eq[0].this.lhs.apply(algebra.ceiling.to.floor)

    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.add.quotient)


if __name__ == '__main__':
    run()
# created on 2019-03-07
