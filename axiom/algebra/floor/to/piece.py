from util import *


@apply
def apply(self):
    n, S[2] = self.of(Floor[Expr / Expr])
    assert n.is_integer
    return Equal(self, Piecewise((n / 2, Equal(n % 2, 0)), ((n - 1) / 2, True)))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True)
    Eq << apply(n // 2)

    Eq << Eq[0].this.lhs.apply(algebra.floor.to.mul.div)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << Eq[-1] * -2

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.piece, simplify=None)

    Eq << algebra.mod.to.piece.apply(Eq[-1].lhs)

    


if __name__ == '__main__':
    run()
# created on 2022-01-20
# updated on 2022-01-23
