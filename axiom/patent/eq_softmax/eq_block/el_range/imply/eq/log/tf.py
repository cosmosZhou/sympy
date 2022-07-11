from util import *


@apply
def apply(eq_z, eq_z_quote, el):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z_quote = \
    eq_z_quote.of(Equal[BlockMatrix[1][
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

    assert n >= 2 and u >= 2 and l >= 2

    (S[A], (([S[l - 1]], [S[u - 1]]), S[oo])), z = eq_z.of(Equal[Softmax[Add[Mul[BandPart[OneMatrix] - 1]]]])

    (h, S[i]), ((S[i], S[l - 1]), (S[n - i], S[u])) = el.of(Element[Indexed, Range[-Min, Min]])

    return Equal(log(z[i, h[i] + i]), z_quote[i, h[i] + Min(l, n) - 1])


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    n, l, u = Symbol(domain=Range(2, oo))
    h = Symbol(integer=True, shape=(n,))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, n), extended_real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z_quote = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(
        Equal(z, softmax(A + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo)),
        Equal(z_quote, BlockMatrix[1](
            BlockMatrix(
                Lamda[i:Min(l, n) - 1](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i, :i])),
                Lamda[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])),
            BlockMatrix(
                Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
                Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1))))) - Lamda[i:n](OneMatrix(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))),
        Element(h[i], Range(-Min(i, l - 1), Min(n - i, u))))

    Eq << keras.eq_block.imply.eq.softmax.st.logsumexp.tf.apply(Eq[1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])

    i = Eq[2].lhs.index
    Eq << Eq[-1][i]

    Eq.eq = Eq[-1][i + h[i]]

    Eq.ge_neg_min, Eq.lt_min = sets.el_range.imply.et.apply(Eq[2])

    Eq <<= Eq.ge_neg_min.this.find(Min).args[0].apply(algebra.expr.to.piece, upper=n - 1), Eq.lt_min.this.find(Min).args[0].apply(algebra.expr.to.piece, upper=n)

    Eq <<= -Eq[-2].this(i).find(GreaterEqual).simplify(), Eq[-1].this(i).find(GreaterEqual).simplify()

    Eq.lt = algebra.lt.imply.lt.relax.apply(Eq[-1], upper=Min(n, u))

    Eq << algebra.le.imply.le.relax.apply(Eq[-2], upper=Min(l - 1, n - 1))

    Eq.ge = -Eq[-1].this.rhs.apply(algebra.min.to.add)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq.ge, Eq.eq, invert=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq.lt, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.add_piece.to.piece)

    Eq << algebra.eq.imply.eq.log.apply(Eq[-1])

    Eq.loss = -algebra.eq.imply.eq.sum.apply(Eq[3] * (1 + log(1 + abs(h[i]) / 2)), (i, 0, n))




if __name__ == '__main__':
    run()
# created on 2022-01-05
