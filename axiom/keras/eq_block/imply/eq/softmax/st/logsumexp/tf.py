from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], S[n + 1 - Min(n, u)])), (S[A[i + n - Min(n, u) + 1, i + n - Min(n, u) + 1:n]], (S[i], S[0], S[Min(n, u) - 1])))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
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
            Lamda[Sliced[Tuple[Add[Min]]]],
            Lamda[
                BlockMatrix[
                    NegativeInfinity * OneMatrix
                    ]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:Min(l, n) - 1](BlockMatrix(Exp(z[i, Min(l, n) - 1 - i:Min(l, n) - 1]), ZeroMatrix(n - i))),
        Lamda[i:n - Min(l, n) + 1](BlockMatrix(ZeroMatrix(i), Exp(z[i + Min(l, n) - 1,:Min(l, n) - 1]), ZeroMatrix(n - i - Min(l, n) + 1)))) + BlockMatrix(
        Lamda[i:n - Min(u, n) + 1](BlockMatrix(ZeroMatrix(i), Exp(z[i, Min(l, n) - 1:]), ZeroMatrix(n - i - Min(u, n)))),
        Lamda[i:Min(u, n) - 1](BlockMatrix(ZeroMatrix(n - Min(u, n) + i + 1), Exp(z[i + n - Min(u, n) + 1, Min(l, n) - 1:breadth - i - 1])))))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n) - 1](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i,:i])),
            Lamda[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])),
        BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1))))) - Lamda[i:n](OneMatrix(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))))

    Eq << algebra.eq.imply.eq.exp.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(Exp[Lamda[BlockMatrix]]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(algebra.exp.to.block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Lamda]]).apply(algebra.exp.to.lamda)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(algebra.pow.to.mul.OneMatrix)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.pow)

    Eq << keras.eq_block.imply.eq.softmax.st.exp.tf.apply(Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2022-03-15
