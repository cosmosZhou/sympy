from util import *


@apply
def apply(eq, a):
    Ξ = eq.of(Equal[Identity + BlockMatrix[BlockMatrix[1][ZeroMatrix, OneMatrix], BlockMatrix[1][OneMatrix, ZeroMatrix]]])
    return Equal(exp(a + (Ξ - 1) * oo), Ξ * exp(a))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n = Symbol(integer=True, positive=True)
    h = Symbol(domain=Range(1, n))
    a = Symbol(shape=(n, n), real=True)
    Ξ = Symbol(real=True, shape=(n, n))
    Eq << apply(Equal(Ξ, Identity(n) + BlockMatrix([[ZeroMatrix(h, h), OneMatrix(h, n - h)],
                                                [OneMatrix(n - h, h), ZeroMatrix(n - h, n - h)]])), a)

    i, j = Symbol(integer=True)
    Ξ_quote = Symbol("Ξ'", Lamda[j:n, i:n](Bool(Equal(i, j) | (i < h) & (j >= h) | (i >= h) & (j < h))))
    Eq << Ξ_quote[i, j].this.definition

    Eq.Ξ_quote_definition = Eq[-1].this.rhs.apply(algebra.bool.to.piece)

    Eq << Eq[0][i, j]

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.args[0].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.args[1].expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.args[0]().expr.args[1]().expr.simplify()

    Eq.Ξ_definition = Eq[-1].this.rhs.args[1]().expr.simplify()

    Eq << Eq.Ξ_definition.this.rhs.args[-1].expr.apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    Eq << Eq[-1].this.rhs.args[0].expr.apply(algebra.kroneckerDelta.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten, index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.rhs.args[1].cond.apply(algebra.et.collect, cond=i < h)

    Eq << Eq[-1].this.rhs.args[1].cond.apply(algebra.et.collect, cond=j < h)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.find(And).apply(algebra.et.to.ou.collect, cond=Equal(i, j))

    Eq << Eq[-1].this.find(And).apply(algebra.et.to.ou)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.Ξ_quote_definition, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << keras.imply.eq.bert.mask.theorem.apply(a, Ξ_quote, add=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq[1].reversed)

    
    


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2020-12-29
# updated on 2022-02-19
