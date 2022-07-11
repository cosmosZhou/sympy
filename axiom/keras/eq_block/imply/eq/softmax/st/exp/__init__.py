from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), ((((S[A], S[i]), (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u)]), (S[i + n - Min(n, u)], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Lamda[
                BlockMatrix[
                    ZeroMatrix,
                    Exp[Sliced[Indexed]]
                ],
                Tuple[Min]
                ],
            Lamda[Exp]
            ],
        BlockMatrix[
            Lamda[Exp[Sliced[Indexed, Tuple[Add[Min]]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Exp[Sliced[Indexed]],
                    ZeroMatrix
                    ],
                Tuple[Min]
                ]
            ]
        ] / Lamda[OneMatrix * ReducedSum[Exp]]])

    assert n >= 2 and u >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:Min(l, n)](BlockMatrix(z[i, Min(l, n) - i - 1:Min(l, n) - 1], ZeroMatrix(n - i))),
        Lamda[i:n - Min(l, n)](BlockMatrix(ZeroMatrix(i + 1), z[i + Min(l, n), :Min(l, n) - 1], ZeroMatrix(n - i - Min(l, n))))) + BlockMatrix(
        Lamda[i:n - Min(u, n)](BlockMatrix(ZeroMatrix(i), z[i, Min(l, n) - 1:], ZeroMatrix(n - i - Min(u, n)))),
        Lamda[i:Min(u, n)](BlockMatrix(ZeroMatrix(n - Min(u, n) + i), z[i + n - Min(u, n), Min(l, n) - 1:breadth - i]))))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n)](BlockMatrix(ZeroMatrix(Min(l, n) - i - 1), Exp(A[i, :i]))),
            Lamda[i:n - Min(l, n)](Exp(A[i + Min(l, n), i + 1:i + Min(l, n)]))),
        BlockMatrix(
        Lamda[i:n - Min(u, n)](Exp(A[i, i:i + Min(u, n)])),
        Lamda[i:Min(u, n)](BlockMatrix(Exp(A[i + n - Min(u, n), n - Min(u, n) + i:]), ZeroMatrix(i + 1))))) / Lamda[i:n](OneMatrix(breadth) * ReducedSum(Exp(A[i, relu(i + 1 - l):Min(n, i + u)])))))

    Ξ = Symbol(Eq[1].find(BandPart))
    Eq.ksi_def = Ξ.this.definition

    Eq << keras.imply.eq.bert.mask.theorem.apply(A, Ξ, add=True)

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq.a_quote_exp = Eq[-1].subs(Eq.a_quote_def.reversed)

    z = Symbol(Eq[1].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed, Eq.a_quote_def.reversed)

    i = Eq[1].find(Lamda).variable
    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(keras.softmax.to.mul.reducedSum)

    Eq.zi_def = Eq[-1].this.rhs.subs(Eq.a_quote_exp[i])

    Eq << Eq.ksi_def[i].this.find(BandPart).defun()

    Eq.ksi_def = Eq[-1].this.rhs.expr.apply(algebra.bool.to.piece)

    Eq << Eq.zi_def.find(ReducedSum).this.subs(Eq.ksi_def)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Element).apply(sets.el.add, i)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.find(Max).apply(keras.max.to.relu)

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

    Eq << Eq[-1].this.find(Piecewise[ExprCondPair[3]]).apply(algebra.piece.swap, i=0)

    Eq << Eq[-1].this.rhs.args[0].find(Piecewise[ExprCondPair[3]]).apply(algebra.piece.swap, i=0)

    Eq << Eq[-1].this.find(And).apply(sets.et.to.el.range, simplify=None)

    Eq << Eq[-1].this.find(And).apply(sets.et.to.el.range, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, i, simplify=None)

    Eq << Eq[-1].this.find(Element[Symbol]).apply(sets.el.sub, i, simplify=None)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.piece.flatten)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.piece.flatten)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.find(And).apply(algebra.et.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this(i, j).find(And).apply(sets.et_ou.to.el_range.bandPart.lower.st.lt)

    Eq << Eq[-1].this.find(And).apply(algebra.et.collect, cond=Eq[-1].find(Element))

    Eq.zij_dquote_def = Eq[-1].this(i, j).find(And).apply(sets.et_ou.to.el_range.bandPart.upper.min)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j + Min(l, n) - i - 1]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < Symbol).simplify()

    Eq << Eq[-1].this(j).find(Symbol < 0).simplify()

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.zij_def, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_dquote_def, Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-02

from . import tf
# updated on 2022-03-30
