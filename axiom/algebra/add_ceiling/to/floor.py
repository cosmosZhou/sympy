from util import *


@apply
def apply(self):
    n, d = self.of(Ceiling[Expr / Expr] - 1)
    return Equal(self, (n - 1) // d)


@prove
def prove(Eq):
    from axiom import algebra

    n, d = Symbol(integer=True)
    Eq << apply(Ceiling(n / d) - 1)

    Eq << Eq[0].this.find(Ceiling).apply(algebra.ceiling.to.floor)

    Eq << Eq[-1].this.lhs.find(Floor).apply(algebra.floor.to.add.quotient)


if __name__ == '__main__':
    run()
# created on 2018-08-11
