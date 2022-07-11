from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (n, u)))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[Sliced[Indexed, Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix],
                Tuple[Min - 1]]] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2
    return Equal(ReducedArgMax(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z))


@prove
def prove(Eq):
    from axiom import patent, algebra

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    z = Symbol(shape=(n, Min(u, n)), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1)))) - Lamda[i:n](OneMatrix(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << patent.eq_block.imply.eq.softmax.upper_triangle.st.logsumexp.tf.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq << Eq[-1].subs(z_quote.this.definition.reversed)

    Eq << algebra.eq.imply.eq.reducedArgMax.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.reducedArgMax.to.block.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Lamda]).apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.add)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(algebra.reducedArgMax_exp.to.reducedArgMax)

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.lamda.piece)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.to.add)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.add)

    Eq.eq_reducedArgMax = Eq[-1].this.find(Lamda[Piecewise]).apply(algebra.lamda_piece.to.block)

    Eq.eq_lamda = Equal(
        Lamda[i:Min(u, n) - 1](z[i + n + 1 - Min(n, u)]),
        Lamda[i:Min(u, n) - 1](BlockMatrix(z[i + n + 1 - Min(n, u), :Min(u, n) - i - 1], -oo * OneMatrix(i + 1))),
        plausible=True)

    i_ = Symbol("i", domain=Range(Min(u, n) - 1))
    Eq << algebra.eq.given.eq.getitem.apply(Eq.eq_lamda, i_)

    j_ = Symbol("j", domain=Range(Min(u, n)))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j_)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(algebra.eq.transport)

    j = Symbol(integer=True)
    Eq << Eq[0][i + n + 1 - Min(n, u), j - i]

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, i, Min(u, n) - 1))

    Eq.zi_min_def = Eq[-1].this(i).find(Lamda)(j).find(Less[Add, Min - 1]).simplify()

    Eq << Eq.eq_lamda.subs(Eq.zi_min_def)

    Eq << algebra.eq.imply.eq.reducedArgMax.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.reducedArgMax.to.lamda.reducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(algebra.reducedArgMax_block.to.reducedArgMax)

    Eq << Eq[-1].subs(Eq.zi_min_def.reversed)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedArgMax.to.lamda.reducedArgMax, simplify=None).reversed

    Eq << Eq.eq_reducedArgMax.subs(Eq[-1])

    Eq << Eq[-1].this.find(BlockMatrix).apply(algebra.block.to.lamda.piece)

    Eq << Eq[-1].this.apply(algebra.eq.transport, rhs=0)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.reducedArgMax)

    Eq << Eq[-1].this.lhs.find(ReducedArgMax).arg.definition




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2022-01-15
