from util import *


@apply
def apply(self):
    plus, d = self.of(Floor[Expr / Expr])
    n = plus - (d - 1)

    return Equal(self, ceiling(n / d))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True, positive=True)
    Eq << apply(n // d)

    Eq << algebra.ceiling.to.floor.apply(Eq[0].rhs).reversed


if __name__ == '__main__':
    run()
