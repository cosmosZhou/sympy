from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l, i + 1:i + l + 1], (S[i], S[0], (n, S[l])))), (A[i, relu(i - l + 1):i + 1], (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Sliced[Indexed]
                    ],
                ],
                Lamda[Tuple[Expr - Expr]]
                ] - Lamda[OneMatrix * logsumexp]
            ])

    assert n >= 2 and l >= 2 and l <= n
    return Equal(ReducedArgMax(softmax(A + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z) - l + 1)


@prove
def prove(Eq):
    from axiom import patent, algebra

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, l), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) - Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))))

    Eq << patent.eq_block.imply.eq.softmax.lower_triangle.st.logsumexp.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq << Eq[-1].subs(z_quote.this.definition.reversed)

    Eq << algebra.eq.imply.eq.reducedArgMax.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.reducedArgMax.to.block.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Lamda]).apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq.eq_reducedArgMax = Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq.eq_lamda = Equal(
        Lamda[i:Min(l, n)](z[i]),
        Lamda[i:Min(l, n)](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), z[i, Min(l, n) - i - 1:])),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(l, n)))
    Eq << algebra.eq.given.eq.getitem.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(l, n)))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(algebra.eq.transport)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    j = Symbol(integer=True)
    Eq << Eq[0][i, j + Min(l, n) - i - 1]

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, i + 1))

    Eq.zi_min_def = Eq[-1].this.find(Lamda)(j).find(Symbol < 0).simplify()

    Eq << Eq.eq_lamda.subs(Eq.zi_min_def)

    Eq << algebra.eq.imply.eq.reducedArgMax.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq << Eq[-1].subs(Eq.zi_min_def.reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=slice(0, 2)).reversed

    Eq << Eq[-1].this.lhs.apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.apply(algebra.eq.transport, lhs=0)

    Eq << Eq.eq_reducedArgMax.subs(Eq[-1])

    Eq << Eq[-1].this.find(Lamda + Lamda).apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.lamda.piece)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq << Eq[-1].this.find(Lamda[2]).apply(algebra.lamda.to.reducedArgMax)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=3)

    Eq << Eq[-1].this.find(ReducedArgMax).arg.definition





if __name__ == '__main__':
    run()
# created on 2022-01-03

from . import tf
# updated on 2022-03-30
