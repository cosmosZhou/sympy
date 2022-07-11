from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (A[i + n - Min(n, u), i + n - Min(n, u):], (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[
                Exp[Sliced[Indexed, Tuple[Add]]],
                Tuple[Expr - Expr]],
            Lamda[
                BlockMatrix[
                    Exp,
                    ZeroMatrix
                ],
            ]
        ] / Lamda[OneMatrix * ReducedSum[Exp]]])

    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:n - u](BlockMatrix(ZeroMatrix(i), z[i], ZeroMatrix(n - i - u))),
        Lamda[i:u](BlockMatrix(ZeroMatrix(n - u + i), z[i + n - u, :u - i]))))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, u), real=True)
    Eq << apply(Equal(z, BlockMatrix(
        Lamda[i:n - u](Exp(A[i, i:i + u])),
        Lamda[i:u](BlockMatrix(Exp(A[i + n - u, n - u + i:]), ZeroMatrix(i)))) / Lamda[i:n](OneMatrix(u) * ReducedSum(Exp(A[i, i:Min(n, i + u)])))))

    i = Eq[1].find(Lamda).variable
    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << keras.imply.eq.bert.mask.theorem.apply(A, Ξ, add=True)

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(keras.softmax.to.mul.reducedSum)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(algebra.bool.to.piece)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Element).apply(sets.el.add, i)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this(i).find(Max).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq.zij_def = Eq[-1].this.find(Mul).apply(algebra.mul.to.piece)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair).expr.apply(algebra.piece.swap, i=0)

    Eq << Eq[-1].this.find(And).apply(sets.et.to.el.range, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, i, simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(algebra.piece.swap, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j - i]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < Symbol).simplify()

    Eq << Eq[-1].this.find(And).apply(algebra.et.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this(i, j).find(And).apply(sets.et_ou.to.el_range.bandPart.upper)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.zij_def, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_dquote_def, Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-02

# updated on 2022-03-30
from . import tf
