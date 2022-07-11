from util import *


@apply
def apply(eq):
    (H, ((((Q, i), W, (K, (S[0], S[i + 1]))), (S[i], S[0], l)), ((S[Q[i + l]], S[W], S[K[i + 1:i + l + 1].T]), (S[i], S[0], (n, S[l])))), (((S[Q[i]], S[W], S[K[relu(i - l + 1):i + 1].T]), S[H[i]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][ZeroMatrix, Expr] + BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Indexed @ Expr @ Transpose[Sliced]
                    ],
                ],
                Lamda[MatMul, Tuple[Expr - Expr]]
            ] - Lamda[OneMatrix * logsumexp[MatMul + BlockMatrix[ZeroMatrix, Expr]]]])
    assert n >= 2 and l >= 2 and l <= n    
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), ZeroMatrix(n - 1 - i))),
                     Lamda[i:n - l](BlockMatrix(ZeroMatrix(i + 1), Exp(z[i + l]), ZeroMatrix(n - 1 - i - l)))))


@prove
def prove(Eq):
    from axiom import patent

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    d_z = Symbol(integer=True, positive=True)
    Q, K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, l), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](ZeroMatrix(n, l - 1), H) + BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), Q[i] @ W @ K[:i + 1].T)),
            Lamda[i:n - l](Q[i + l] @ W @ K[i + 1:i + l + 1].T)) - Lamda[i:n](OneMatrix(l) * logsumexp((Q[i] @ W @ K[relu(i + 1 - l):i + 1].T + BlockMatrix(ZeroMatrix(Min(i, l - 1)), H[i]))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i + 1]

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n) + 1]

    Eq << Eq.A_def[i][relu(i + 1 - l):i + 1]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << patent.eq_block.imply.eq.softmax.biased.lower_triangle.st.logsumexp.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-04

from . import tf
# updated on 2022-03-29
