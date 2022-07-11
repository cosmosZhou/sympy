from util import *


@apply
def apply(eq):
#   (H, ((((Q, i), W, (K, (  i , (  i , (n, u))))), (  i ,   0 ,   n - Min(n, u) + 1) ), ((  Q[i + n - Min(n, u) + 1] ,   W ,   K[i + n - Min(n, u) + 1:].T ), (  i ,   0 ,   Min(n, u) - 1 ))), (((  Q[i] ,   W ,   K[i:Min(n, i + u)].T ),   H[i] ), (  i ,   0 ,   n ))), z
    (H, ((((Q, i), W, (K, (S[i], (S[i], (n, u))))), (S[i], S[0], S[n - Min(n, u) + 1])), ((S[Q[i + n - Min(u, n) + 1]], S[W], S[K[i + n - Min(n, u) + 1:].T]), (S[i], S[0], S[Min(u, n) - 1]))), (((S[Q[i]], S[W], S[K[i:Min(n, i + u)].T]), S[H[i]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, ZeroMatrix] + BlockMatrix[
                Lamda[Indexed @ Expr @ Transpose[Sliced[Tuple[Add[Min]]]]],
                Lamda[
                    BlockMatrix[
                        MatMul,
                        NegativeInfinity * OneMatrix
                    ],
                ]
            ] - Lamda[OneMatrix * logsumexp[MatMul + BlockMatrix[Expr, ZeroMatrix]]]])
    assert n >= 2 and u >= 2
    breadth = Min(u, n) - 1
    return Equal(softmax(Q @ W @ K.T + H * Identity(n) + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:n - breadth](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - 1 - i - breadth))),
                     Lamda[i:breadth](BlockMatrix(ZeroMatrix(n - breadth + i), Exp(z[i + n - breadth, :breadth - i])))))


@prove
def prove(Eq):
    from axiom import algebra, patent

    n, u = Symbol(domain=Range(2, oo))
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z, d_z), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, Min(u, n)), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, ZeroMatrix(n, Min(u, n) - 1)) + BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](Q[i] @ W @ K[i:i + Min(u, n)].T),
            Lamda[i:Min(u, n) - 1](BlockMatrix(Q[i + n - Min(u, n) + 1] @ W @ K[n - Min(u, n) + i + 1:].T, -oo * OneMatrix(i + 1)))) - Lamda[i:n](OneMatrix(Min(u, n)) * logsumexp((Q[i] @ W @ K[i:Min(n, i + u)].T + BlockMatrix(H[i], ZeroMatrix(Min(n - i, u) - 1)))))))

    A = Symbol(Eq[1].find(MatMul))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n + 1 - Min(u, n)))

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq.A_def[i + n + 1 - Min(u, n)][i + n + 1 - Min(u, n):]

    Eq << Eq[0].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << patent.eq_block.imply.eq.softmax.biased.upper_triangle.st.logsumexp.tf.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_def)

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2022-03-14
