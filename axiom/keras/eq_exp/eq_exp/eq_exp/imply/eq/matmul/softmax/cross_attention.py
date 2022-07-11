from util import *


@apply
def apply(eq_D, eq_Ah, eq_Al, V):
    # diagonal part
    ((K, Q), d_z), D = eq_D.of(Equal[Transpose[OneMatrix * Exp[ReducedSum[Mul] * Expr ** (-S.One / 2)]]])
    n, S[d_z] = Q.shape
    # upper part
    (((S[Q], (S[0], h)), (S[K], (S[h], S[n]))), S[1 / sqrt(d_z)]), Ah = eq_Ah.of(Equal[Exp[Mul[Sliced @ Transpose[Sliced]]]])

    Vu = V[:h]
    Du = D[:h]

    # lower part
    (((S[Q], (S[h], S[n])), (S[K], (S[0], S[h]))), S[1 / sqrt(d_z)]), Al = eq_Al.of(Equal[Exp[Mul[Sliced @ Transpose[Sliced]]]])
    Vl = V[h:n]
    Dl = D[h:n]

    return Equal(softmax(Q @ K.T / sqrt(d_z) + (-1 + Identity(n) + BlockMatrix([[ZeroMatrix(h, h), OneMatrix(h, n - h)],
                                            [OneMatrix(n - h, h), ZeroMatrix(n - h, n - h)]])) * oo) @ V, BlockMatrix((Ah @ Vl + Du * Vu) / (ReducedSum(Ah) + Du), (Al @ Vu + Dl * Vl) / (ReducedSum(Al) + Dl)))


@prove
def prove(Eq):
    from axiom import keras, discrete, algebra

    n, d_z = Symbol(integer=True, positive=True)
    h = Symbol(domain=Range(1, n))
    Q, K, V, D = Symbol(shape=(n, d_z), real=True)
    Ah = Symbol(shape=(h, n - h), real=True)
    Al = Symbol(shape=(n - h, h), real=True)
    Eq << apply(
        Equal(D, (exp(ReducedSum(Q * K) / sqrt(d_z)) * OneMatrix(d_z, n)).T),
        Equal(Ah, exp(Q[:h] @ K[h:n].T / sqrt(d_z))),
        Equal(Al, exp(Q[h:n] @ K[:h].T / sqrt(d_z))), V)

    i = Symbol(domain=Range(n))
    j = Symbol(integer=True)
    a = Symbol(Eq[-1].find(Mul[MatMul]))
    Eq.a_def = a.this.definition

    z = Symbol(Eq[-1].lhs)
    Ξ = Symbol(Eq[-1].find(Mul[Infinity, ~Add]) + 1)
    Eq.ksi_def = Ξ.this.definition

    Eq << keras.eq_add_block.imply.eq.mask.cross_attention.apply(Eq.ksi_def, a)

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

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.piece)

    Eq << Eq[-1].this.find(ExprCondPair)().expr.args[0].simplify()

    Eq << Eq[-1].this.find(ExprCondPair[2]).expr.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(ExprCondPair)().find(Sum)().expr.simplify()

    Eq << Eq[-1].this.find(ExprCondPair[2])().find(Sum)().expr.simplify()

    Eq << Eq[-1].this.rhs.simplify(wrt=True)

    Eq.divisor_definition = Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << Eq.divisor_definition.find(ExprCondPair[2]).find(Sum).this.apply(algebra.sum.to.reducedSum)

    Eq << Eq.divisor_definition.find(ExprCondPair).find(Sum).this.apply(algebra.sum.to.reducedSum)

    Eq.divisor_definition = Eq.divisor_definition.this.rhs.subs(Eq[-2], Eq[-1], simplify=False)

    Eq << Eq[0][i]

    Eq << Eq[-1].this.find(ReducedSum).apply(discrete.reducedSum.to.matmul)

    Eq.M_definition = Eq[-1].this.find(MatMul).T

    Eq << Eq.a_def[i]

    Eq <<= Eq[-1][h:n], Eq[-1][:h], Eq[-1][i]

    Eq <<= algebra.eq.imply.eq.exp.apply(Eq[-3]), algebra.eq.imply.eq.exp.apply(Eq[-2]), algebra.eq.imply.eq.exp.apply(Eq[-1])

    Eq << Eq[-1] * OneMatrix(d_z)

    Eq.lower_part, Eq.upper_part, Eq.diagonal_part = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq[1][i]), \
        algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[2][i - h]), \
        algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq.M_definition)

    Eq << Eq.divisor_definition * OneMatrix(d_z)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.subs(Eq.lower_part, Eq.upper_part, Eq.diagonal_part)

    Eq.zi_definition = algebra.eq.cond.imply.cond.subs_with_expand_dims.apply(Eq[-1], Eq.zi_definition)

    Eq << Eq.zi_definition.find(MatMul).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum[~Mul]).args[1].definition

    Eq << Eq[-1].this(i).find(ExprCondPair)().expr.simplify()

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.rhs.expr.simplify(wrt=i)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.piece.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum_mul.to.add)

    Eq << Eq[-1].this.find(ExprCondPair)().find(Piecewise).simplify()

    Eq << Eq[-1].this.find(Sum[Mul[Add]]).apply(algebra.sum_mul.to.add)

    Eq << Eq[-1].this.find(ExprCondPair[2])().find(Piecewise).simplify()

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.piece)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul).T

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq[-1].this.rhs.find(MatMul[Lamda]).T

    Eq << Eq[-1].this.rhs.subs(Eq.lower_part, Eq.upper_part)

    Eq << algebra.eq.cond.imply.cond.subs_with_expand_dims.apply(Eq.diagonal_part, Eq[-1])

    Eq << Eq.zi_definition.this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piece.to.piece)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i,))

    Eq << Eq[-1].this.rhs.apply(algebra.lamda_piece.to.block)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(~Lamda * Lamda).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.find(Lamda[Mul]).apply(algebra.lamda.to.mul)

    Eq << Eq[-1].this.find(~Lamda * Lamda).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.reducedSum)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.reducedSum)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_def, Eq[-1])

    
    


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2021-01-02
# updated on 2022-04-01
