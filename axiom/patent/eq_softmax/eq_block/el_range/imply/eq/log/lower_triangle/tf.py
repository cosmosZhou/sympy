from util import *


@apply
def apply(eq_z, eq_z_quote, el):
    (((((A, i), (S[0], S[i + 1])), (S[i], S[0], l)), (A[i + l - 1, i:i + l], (S[i], S[0], (n, S[l])))), (A[i, relu(i - l + 1):i + 1], (S[i], S[0], S[n]))), z_quote = \
    eq_z_quote.of(Equal[
        BlockMatrix[
            Lamda[
                BlockMatrix[
                    NegativeInfinity * OneMatrix,
                    Sliced[Indexed]
                ],
                Tuple[Expr - 1]
            ],
            Lamda[Tuple[Expr + 1 - Expr]]
        ] - Lamda[OneMatrix * logsumexp]])

    (S[A], (([S[l - 1]], [S[0]]), S[oo])), z = eq_z.of(Equal[Softmax[Add[Mul[BandPart[OneMatrix] - 1]]]])

    assert n >= 2 and l >= 2 and l <= n

    (h, i), (S[i], S[l - 1]) = el.of(Element[Indexed, Range[-Min, 1]])

    return Equal(log(z[i, h[i] + i]), z_quote[i, h[i] + l - 1])


@prove
def prove(Eq):
    from axiom import patent, algebra, sets

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    h = Symbol(integer=True, shape=(n,))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, n), extended_real=True)
    z_quote = Symbol(shape=(n, l), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(
        Equal(z, softmax(A + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo)),
        Equal(z_quote, BlockMatrix(
            Lamda[i:l - 1](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l + 1](A[i + l - 1, i:i + l])) - Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))),
        Element(h[i], Range(-Min(i, l - 1), 1)))

    Eq << patent.eq_block.imply.eq.softmax.lower_triangle.st.logsumexp.tf.apply(Eq[1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])

    i = Eq[2].lhs.index
    Eq << Eq[-1][i]

    Eq.eq = Eq[-1][i + h[i]]

    Eq.ge_relu, Eq.lt_1 = sets.el_range.imply.et.apply(Eq[2])

    Eq << Eq.ge_relu.this.find(Min).args[0].apply(algebra.expr.to.piece, upper=n - 1)

    Eq << Eq[-1].this(i).find(GreaterEqual).simplify()

    Eq << -Eq[-1]

    Eq.ge = -algebra.le.imply.le.relax.apply(Eq[-1], upper=l - 1)

    

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq.ge, Eq.eq, invert=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq.lt_1, Eq[-1])

    Eq << algebra.eq.imply.eq.log.apply(Eq[-1])

    Eq.loss = -algebra.eq.imply.eq.sum.apply(Eq[3] * (1 + log(1 - h[i] / 2)), (i, 0, n))

    
    


if __name__ == '__main__':
    run()
# created on 2021-12-17
# updated on 2022-03-30
