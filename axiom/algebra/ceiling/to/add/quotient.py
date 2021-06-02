from util import *


@apply
def apply(self):
    import axiom
    div = self.of(Ceiling)
    n, d = axiom.is_Divide(div)

    return Equal(self, (n - 1) // d + 1)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True)
    d = Symbol.d(integer=True)
    Eq << apply(ceiling(n / d))

    Eq << Eq[0].this.lhs.apply(algebra.ceiling.to.floor)

    Eq << Eq[-1].this.lhs.apply(algebra.floor.to.add.quotient)


if __name__ == '__main__':
    run()