from util import *


@apply
def apply(self):
    assert self.is_Bool
    et = self.of(Bool)
    eqs = et.of(And)

    return Equal(self, Mul(*(Bool(eq)for eq in eqs)))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True)
    Eq << apply(Bool((x > y) & (a > b)))

    Eq << Eq[0].this.rhs.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten, index=0)

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

# created on 2018-02-14
