from util import *


@apply
def apply(n):
    i, j = Symbol(integer=True)

    return Equal(Lamda[j:n, i:n](Piecewise((i, j < i), (j, j > i), (0, True))),
                 (1 - Identity(n)) * Lamda[j:n, i:n](Max(i, j)))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    Eq << apply(n)

    i, j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], (i, j))

    Eq << Eq[-1].this.find(Max).apply(algebra.max.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << Eq[-1].this.rhs.simplify(wrt=i)

    Eq << Eq[-1].this.find(GreaterEqual).reversed

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul_piece.to.piece, simplify=False)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(algebra.add.to.piece, simplify=False)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(algebra.mul_piece.to.piece, simplify=False)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten, index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.invert, 0)

    Eq << Eq[-1].this.lhs.find(Equal).reversed


if __name__ == '__main__':
    run()
# created on 2019-10-17
