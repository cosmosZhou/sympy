from util import *


@apply
def apply(eq_Ah, eq_Al, V):
    # upper part
    (((Q, (S[0], h)), (K, (S[h], n))), sqrt_dz), Ah = eq_Ah.of(Equal[Exp[Mul[Sliced @ Transpose[Sliced]]]])
    Vu = V[:h]
    d_z = sqrt_dz.of(Expr ** (-S.One / 2))    

    # lower part
    (((S[Q], (S[h], S[n])), (S[K], (S[0], S[h]))), S[1 / sqrt(d_z)]), Al = eq_Al.of(Equal[Exp[Mul[Sliced @ Transpose[Sliced]]]])
    Vl = V[h:n]

    return Equal(softmax(Q @ K.T / sqrt(d_z) + (-1 + BlockMatrix([[ZeroMatrix(h, h), OneMatrix(h, n - h)],
                                            [OneMatrix(n - h, h), ZeroMatrix(n - h, n - h)]])) * oo) @ V, BlockMatrix((Ah @ Vl) / ReducedSum(Ah), Al @ Vu / ReducedSum(Al)))


@prove
def prove(Eq):
    from axiom import keras, discrete, algebra

    n, d_z = Symbol(integer=True, positive=True)
    h = Symbol(domain=Range(1, n))
    Q, K, V = Symbol(shape=(n, d_z), real=True)
    Ah = Symbol(shape=(h, n - h), real=True)
    Al = Symbol(shape=(n - h, h), real=True)
    Eq << apply(
        Equal(Ah, exp(Q[:h] @ K[h:n].T / sqrt(d_z))),
        Equal(Al, exp(Q[h:n] @ K[:h].T / sqrt(d_z))), V)

    i = Symbol(domain=Range(n))
    j = Symbol(integer=True)
    a = Symbol(Eq[-1].find(Mul[MatMul]))
    Eq.a_def = a.this.definition

    z = Symbol(Eq[-1].lhs)
    Ξ = Symbol(Eq[-1].find(Mul[Infinity, ~Add]) + 1)
    Eq.ksi_def = Ξ.this.definition

    Eq << keras.eq_block.imply.eq.mask.cross_attention.apply(Eq.ksi_def, a)

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq.a_quote_def = a_quote.this.definition

    Eq << Eq[-1].subs(Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq.z_def = z.this.definition

    Eq << Eq.z_def.subs(Eq.ksi_def.reversed).subs(Eq.a_def.reversed).subs(Eq.a_quote_def.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.find(softmax).apply(keras.softmax.to.mul.reducedSum)

    Eq.zi_definition = Eq[-1].this.rhs.subs(Eq[-4])

    Eq << Eq.zi_definition.find(ReducedSum).this.apply(discrete.reducedSum.to.matmul)

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.subs(Eq.ksi_def)

    Eq.divisor_definition = Eq[-1].this.rhs.apply(algebra.sum.to.piece)

    Eq << Eq.divisor_definition.find(ExprCondPair[2]).find(Sum).this.apply(algebra.sum.to.reducedSum)

    Eq << Eq.divisor_definition.find(ExprCondPair).find(Sum).this.apply(algebra.sum.to.reducedSum)

    Eq.divisor_definition = Eq.divisor_definition.this.rhs.subs(Eq[-2], Eq[-1], simplify=False)

    Eq << Eq.a_def[i]

    Eq <<= Eq[-1][h:n], Eq[-1][:h]

    Eq <<= algebra.eq.imply.eq.exp.apply(Eq[-2]), algebra.eq.imply.eq.exp.apply(Eq[-1])

    Eq.lower_part, Eq.upper_part = algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[0][i]), \
        algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[1][i - h])

    Eq << Eq.divisor_definition.this.rhs.subs(Eq.lower_part, Eq.upper_part)

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.find(MatMul).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum[~Mul]).args[1].definition

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.piece)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul).T

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul[Lamda]).T

    Eq << Eq[-1].this.rhs.subs(Eq.lower_part, Eq.upper_part)

    Eq << Eq.zi_definition.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i,))

    Eq << Eq[-1].this.rhs.apply(algebra.lamda_piece.to.block)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(BlockMatrix[~Lamda]).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(Lamda[Pow]).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.find(Lamda[Pow]).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.reducedSum)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.reducedSum)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2022-02-20
# updated on 2022-04-01
