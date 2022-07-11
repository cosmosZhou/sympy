from util import *


@apply
def apply(eq_cup, subset, Q, K, V):
    cup, m = eq_cup.of(Equal[Card])
    (d, j), (S[j], S[0], S[m]) = cup.of(Cup[FiniteSet[Indexed]])
    n, d_z = Q.shape
    S[cup], (S[0], S[n]) = subset.of(Subset[Expr, Range])
    i = eq_cup.generate_var({j}, integer=True, var='i')
    return Equal(softmax(Q @ K.T / sqrt(d_z) + (Lamda[i:n](Bool(Element(i, cup))) - OneMatrix(n, n)) * oo) @ V, \
                 softmax(Q @ Lamda[j:m](K[d[j]]).T / sqrt(d_z)) @ Lamda[j:m](V[d[j]]))



@prove
def prove(Eq):
    from axiom import keras, algebra, sets, discrete

    n, k, m = Symbol(integer=True, positive=True)
    r = Symbol(shape=(n,), integer=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    d = Symbol(shape=(oo,), integer=True)
    i, j = Symbol(integer=True)
    s = d[:m].cup_finiteset(j)
    Eq << apply(Equal(Card(s), m), Subset(s, Range(n)), Q, K, V)


    a = Symbol(Eq[2].find(Mul[MatMul]))
    Eq.a_def = a.this.definition

    z = Symbol(Eq[2].lhs)
    Eq.z_def = z.this.definition

    Eq << Eq.z_def[i]

    Xi = Symbol(Eq[-1].find(Lamda))
    Eq.Xi_def = Xi.this.definition

    Eq << Eq[-1].this.rhs.subs(Eq.Xi_def.reversed, Eq.a_def[i].reversed)

    Eq << Eq[-1].this.find(softmax).apply(keras.softmax.to.mul.reducedSum)

    Eq << keras.imply.eq.bert.mask.theorem.apply(a[i], Xi, add=True)

    Eq.zi_definition = Eq[-2].subs(Eq[-1])

    Eq << Eq.zi_definition.find(ReducedSum).this.subs(Eq.Xi_def)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.absorb)

    Eq.eq_intersect = sets.subset.imply.eq.intersect.apply(Eq[1])

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << sets.eq_card.imply.eq.reducedSum.apply(Eq[0], Eq[-1].find(Sum))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.find(MatMul).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined.insert)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_def[k]

    Eq << Eq[-2].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.absorb)

    Eq << Eq[-1].subs(Eq.eq_intersect)

    Eq << sets.eq_card.imply.eq.sum.apply(Eq[0], Eq[-1].find(Sum))

    Eq << Eq[-1].this.rhs.apply(discrete.sum.to.matmul)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq.zi_definition.subs(Eq[-1])

    Eq << Eq[-1].this.find(Lamda).apply(keras.lamda_exp.to.mul.softmax)

    Eq << Eq[-1].subs(Eq.a_def)

    Eq << Eq[-1].this.find(Lamda[Mul]).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(Lamda[MatMul]).apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.find(Lamda[Tuple[2]]).apply(algebra.lamda.to.transpose)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.find(Lamda).apply(keras.lamda_softmax.to.softmax)

    Eq << Eq[-1].this.find(Lamda[Mul]).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(Transpose[~Lamda]).limits_subs(k, j)

    Eq << Eq[-1].this.find(Lamda).limits_subs(i, j)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-09
# updated on 2022-01-11