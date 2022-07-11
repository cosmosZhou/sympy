from util import *


@apply
def apply(eq):
    (H, ((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (S[A[i + l, i + 1:i + l + 1]], (S[i], S[0], (n, S[l])))), ((S[H[i]], S[A[i, relu(i - l + 1):i + 1]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][ZeroMatrix, Expr] + BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Sliced[Indexed]
                    ],
                ],
                Lamda[Tuple[Expr - Expr]]
            ] - Lamda[OneMatrix * logsumexp[Add[BlockMatrix[ZeroMatrix, Expr]]]]])
    assert n >= 2 and l >= 2 and l <= n
    return Equal(softmax(A + H * Identity(n) + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), ZeroMatrix(n - 1 - i))),
                     Lamda[i:n - l](BlockMatrix(ZeroMatrix(i + 1), Exp(z[i + l]), ZeroMatrix(n - 1 - i - l)))))


@prove
def prove(Eq):
    from axiom import algebra, patent

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, l), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](ZeroMatrix(n, l - 1), H) + BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) - Lamda[i:n](OneMatrix(l) * logsumexp((A[i, relu(i + 1 - l):i + 1] + BlockMatrix(ZeroMatrix(Min(i, l - 1)), H[i]))))))

    Eq << Eq[0].this.find(BlockMatrix[1]).apply(algebra.block.split, Min(l, n))

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(algebra.add_block.to.block)

    Eq.z_def = Eq[-2].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i + 1]

    Eq << Eq[-1].this.find(Mul).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.block)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.block)

    Eq.matmul_subs = Eq[-1].this.apply(algebra.eq.transport, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add).this.args[0].apply(algebra.expr.to.lamda, i)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.expr.to.lamda)

    Eq << Eq[-1].this.rhs.find(-~Piecewise).find(Less).simplify()

    Eq << Eq[-1].this.rhs.find(-~Piecewise).find(Less).apply(algebra.lt.transport, lhs=slice(0, 3, 2))

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add_piece.to.piece)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq.upper_part = Eq[-1].this.rhs.apply(algebra.lamda.piece.to.block)

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n) + 1]

    Eq << Eq[-1].this.find(Mul).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.block)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.block)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n - Min(l, n)), simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    Eq.lower_part = Eq[-1].this.find(Lamda[BlockMatrix]).apply(algebra.lamda_block.to.block.lamda)

    Eq << Eq.A_def[i][relu(i + 1 - l):i + 1]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.offset, -Eq[-1].find(relu))

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(algebra.mul.to.block)

    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq.upper_part, Eq.lower_part.reversed)

    Eq << patent.eq_block.imply.eq.softmax.lower_triangle.st.logsumexp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition





if __name__ == '__main__':
    run()
# created on 2022-03-13
from . import tf
# updated on 2022-03-29
