from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
        BlockMatrix[
            Lamda[
                BlockMatrix[
                    NegativeInfinity * OneMatrix,
                    Sliced[Indexed]
                ],
                Tuple[Min - 1]
                ],
            Lamda
            ],
        BlockMatrix[
            Lamda[Sliced[Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix
                    ],
                Tuple[Min - 1]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and l >= 2 and u >= 2
    return Equal(ReducedArgMax(softmax(A + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z) - Min(l, n) + 1)


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n) - 1](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i, :i])),
            Lamda[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])),
        BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1))))) - Lamda[i:n](OneMatrix(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))))

    Eq << keras.eq_block.imply.eq.softmax.st.logsumexp.tf.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq.z_quote_def = z_quote.this.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.z_quote_def, Eq[-1])

    Eq << Eq[-1][i]

    Eq.four_blocks = Eq[-1].this.rhs.apply(algebra.add_piece.to.piece)

    j = Symbol(integer=True)
    Eq << Eq.four_blocks.find(Add[BlockMatrix]).this.apply(algebra.expr.to.lamda, j)

    Eq << Eq[-1].this.find(Piecewise[2]).apply(algebra.piece.swap, 0)

    Eq.block0 = Eq[-1].this.rhs.apply(algebra.lamda_piece.to.block)

    Eq << Eq.four_blocks.find(ExprCondPair[2]).find(BlockMatrix).this.apply(algebra.expr.to.lamda, j)

    Eq.block1 = Eq[-1].this.rhs.apply(algebra.lamda.to.exp)

    Eq << Eq.four_blocks.find(ExprCondPair[3]).find(Add[BlockMatrix]).this.apply(algebra.expr.to.lamda, j)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap, 0)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap, 0)

    Eq << Eq[-1].this.find(And).apply(algebra.et.to.ou)

    Eq.block2 = Eq[-1].this.find(Lamda).apply(algebra.lamda_piece.to.block)

    Eq << Eq.four_blocks.find(ExprCondPair[4]).find(Add[BlockMatrix]).this.apply(algebra.expr.to.lamda, j)

    Eq << Eq[-1].this.find(Piecewise[ExprCondPair[3]]).apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(algebra.add_piece.to.piece)

    Eq.block3 = Eq[-1].this.find(Lamda).apply(algebra.lamda_piece.to.block)

    Eq << Eq.four_blocks.subs(Eq.block0, Eq.block1, Eq.block2, Eq.block3)

    Eq << algebra.eq.imply.eq.reducedArgMax.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.reducedArgMax.to.piece.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap, -2)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.invert, 1)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.invert)

    Eq << Eq[-1].this.find(And).apply(algebra.et_lt.to.lt.min)

    Eq << Eq[-1].this.find(And).apply(sets.et.to.el.range)

    Eq.four_blocks = Eq[-1].this.find(And).apply(algebra.et_ge.to.ge.max)

    Eq << keras.eq_block.imply.et.infer.block.tf.apply(Eq[0])

    Eq <<= Eq[-3].this.rhs.apply(algebra.eq.imply.eq.reducedArgMax), Eq[-2].this.rhs.apply(algebra.eq.imply.eq.reducedArgMax), Eq[-1].this.rhs.apply(algebra.eq.imply.eq.reducedArgMax)

    Eq <<= Eq[-3].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add), \
        Eq[-2].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq.block3 = Eq[-3].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq.block0 = Eq[-2].this.rhs.apply(algebra.eq.transport, rhs=slice(0, 3))

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq.block1 = Eq[-1].this.rhs.apply(algebra.eq.transport, rhs=slice(0, 3))

    Eq << algebra.infer.imply.eq.piece.apply(Eq.block0, Eq.four_blocks.rhs, index=0, reverse=True)

    Eq << algebra.infer.imply.eq.piece.apply(Eq.block1, Eq[-1].rhs, index=1, reverse=True)

    Eq << algebra.infer.imply.eq.piece.apply(Eq.block3, Eq[-1].rhs, index=1, reverse=True)

    Eq << algebra.et_eq.imply.eq.transit.apply(Eq.four_blocks & Eq[-1] & Eq[-2] & Eq[-3])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(algebra.lamda.to.reducedArgMax)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda[ReducedArgMax]).apply(algebra.lamda.to.reducedArgMax)

    Eq << Eq[-1].subs(Eq.z_quote_def)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=3)





if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2022-01-28
