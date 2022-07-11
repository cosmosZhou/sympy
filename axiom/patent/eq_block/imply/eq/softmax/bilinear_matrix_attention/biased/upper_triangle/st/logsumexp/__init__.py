from util import *


@apply
def apply(eq):
    (H, ((((Q, i), W, (K, (S[i], (S[i], u)))), (S[i], S[0], (n, S[u]))), ((Q[i + n - u], S[W], S[K[i + n - u:].T]), (S[i], S[0], S[u]))), (((Q[i], S[W], S[K[i:Min(n, i + u)].T]), H[i]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, ZeroMatrix] + BlockMatrix[
                Lamda[
                    Indexed @ Expr @ Transpose[Sliced[Tuple[Add]]],
                    Tuple[Expr - Expr]
                ],                
                Lamda[
                    BlockMatrix[
                        MatMul,
                        NegativeInfinity * OneMatrix
                    ],                    
                ]
            ] - Lamda[OneMatrix * logsumexp[MatMul + BlockMatrix[Expr, ZeroMatrix]]]])
    assert n >= 2 and u >= 2 and u <= n
    
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:n - u](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - i - u))),
                     Lamda[i:u](BlockMatrix(ZeroMatrix(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from axiom import algebra, patent

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, u), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, ZeroMatrix(n, u - 1)) + BlockMatrix(
            Lamda[i:n - u](Q[i] @ W @ K[i:i + u].T),
            Lamda[i:u](BlockMatrix(Q[i + n - u] @ W @ K[n - u + i:].T, -oo * OneMatrix(i)))) - Lamda[i:n](OneMatrix(u) * logsumexp((Q[i] @ W @ K[i:Min(n, i + u)].T + BlockMatrix(H[i], ZeroMatrix(Min(n - i, u) - 1)))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n - Min(u, n)))

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << patent.eq_block.imply.eq.softmax.biased.upper_triangle.st.logsumexp.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2022-03-30
from . import tf
