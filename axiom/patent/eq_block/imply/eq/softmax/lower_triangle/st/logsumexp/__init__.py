from util import *


@apply
def apply(eq):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l, i + 1:i + l + 1], (S[i], S[0], (n, S[l])))), (S[A[i, relu(i - l + 1):i + 1]], (S[i], S[0], S[n]))), z = \
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
    return Equal(softmax(A + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), ZeroMatrix(n - 1 - i))),
        Lamda[i:n - l](BlockMatrix(ZeroMatrix(i + 1), Exp(z[i + l]), ZeroMatrix(n - 1 - i - l)))))


@prove
def prove(Eq):
    from axiom import algebra, patent

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, l), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) - Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))))

    Eq << algebra.eq.imply.eq.exp.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(Exp[Lamda[BlockMatrix]]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Lamda]]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(algebra.pow.to.mul.OneMatrix)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.pow)

    Eq << patent.eq_block.imply.eq.softmax.lower_triangle.st.exp.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2022-03-17

from . import tf
