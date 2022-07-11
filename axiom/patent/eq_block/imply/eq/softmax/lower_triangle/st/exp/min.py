from util import *


@apply
def apply(eq):
#   (((((A, i), (  0 ,   i + 1 )), (  i,    0,  (l, n))), (  A[i + Min(l, n)][i + 1:i + Min(l, n) + 1],  (  i ,   0 ,   n - Min(l, n) ))), (  A[i][relu(i - l + 1):i + 1] , (  i,    0 ,   n ))), z
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n) + 1]], (S[i], S[0], S[n - Min(l, n)]))), (S[A[i, relu(i - l + 1):i + 1]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[BlockMatrix[
                ZeroMatrix,
                Exp[Sliced[Indexed]]],
                Tuple[Min]],
            Lamda[Exp]] / Lamda[OneMatrix * ReducedSum[Exp]]])

    assert n >= 2 and l >= 2

    breadth = Min(l, n)
    return Equal(softmax(A + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:breadth](BlockMatrix(z[i, breadth - i - 1:], ZeroMatrix(n - 1 - i))),
        Lamda[i:n - breadth](BlockMatrix(ZeroMatrix(i + 1), z[i + breadth], ZeroMatrix(n - 1 - i - breadth)))))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n, l = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(l, n)), real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:Min(l, n)](BlockMatrix(ZeroMatrix(Min(l, n) - i - 1), Exp(A[i, :i + 1]))),
            Lamda[i:n - Min(l, n)](Exp(A[i + Min(l, n), i + 1:i + Min(l, n) + 1]))) / Lamda[i:n](OneMatrix(Min(l, n)) * ReducedSum(Exp(A[i, relu(i + 1 - l):i + 1])))))

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

    Eq << Eq[-1].this.find(Max).apply(keras.max.to.relu)

    Eq << Eq[-1].this(i).find(Min).simplify()

    Eq << Eq.zi_def.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Indexed).defun()

    Eq << Eq[-1].this.find(BandPart).defun()

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    j = Eq.ksi_def.rhs.variable
    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.piece)

    Eq.zij_def = Eq[-1].this.find(Element).apply(sets.el.negate)

    z_dquote = Symbol('z^\"', Eq[1].rhs)
    Eq.z_dquote_def = z_dquote.this.definition

    Eq.zi_dquote_def = Eq.z_dquote_def[i]

    Eq << Eq.zi_dquote_def[j]

    Eq << Eq[-1].this.find(ExprCondPair[2]).expr.apply(algebra.piece.swap, i=0)

    Eq << Eq[-1].this.find(And).apply(sets.et.to.el.range)

    Eq << Eq[-1].this.find(Element).apply(sets.el.sub, i)

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    Eq.zij_dquote_def = Eq[-1].this.rhs.apply(algebra.piece.swap, 1)

    Eq.zi_quote_def = Eq[0][i]

    Eq << Eq.zi_quote_def[j + Min(l, n) - i - 1]

    Eq << Eq.zij_dquote_def.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this(j).find(Symbol < 0).simplify()

    Eq << Eq[-1].this.find(And).apply(algebra.et.collect, cond=Eq[-1].find(Element))

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(algebra.lt.to.le.strengthen)

    Eq << Eq[-1].this.find(Symbol < Symbol + 1).apply(algebra.lt.to.le.strengthen)

    Eq << Eq[-1].this(i, j).find(And).apply(sets.et_ou.to.el_range.bandPart.lower.st.le.min)

    Eq << Eq[-1].this.find(Element).apply(sets.el.negate)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.zij_def, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_dquote_def, Eq[-1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-02

# updated on 2022-04-01
