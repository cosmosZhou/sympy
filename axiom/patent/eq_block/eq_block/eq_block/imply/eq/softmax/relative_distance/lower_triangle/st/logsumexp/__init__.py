from util import *


@apply
def apply(eq_V, eq_V_quote, eq):
    ((w, (k, (r_relative, S[-k], S[k]))), j_limit, i_limit), V = eq_V.of(Equal[Lamda[Indexed[Symbol, Add[clip]]]])

    j, S[0], n = j_limit
    i, S[0], S[n] = i_limit

    (r, S[j]), (S[r], S[i]) = r_relative.of(Indexed - Indexed)

    ((S[w], clip_index), (S[j], S[0], l), S[i_limit]), V_quote = eq_V_quote.of(Equal[Lamda[Indexed]])
    S[k], (((S[r], S[Min(j + relu(i - l + 1), n - 1)]), (S[r], S[i])), S[-k], S[k]) = clip_index.of(Add[clip[Indexed - Indexed]])
    ((((((A, i), (S[0], S[i + 1])), V_quote[i, :i + 1]), (S[i], S[0], S[l])), (V_quote[l:], (A[i + l, i + 1:i + l + 1], (S[i], S[0], S[n - l])))), ((A[i, relu(i + 1 - l):i + 1], V_quote[i, :Min(i + 1, l)]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Add[Sliced[Indexed]]
                        ],
                ],
                Add[Lamda]
                ] - Lamda[OneMatrix * logsumexp[Add]]
            ])

    assert n >= 2 and l >= 2 and l <= n

    return Equal(softmax(A + V + (BandPart[l - 1, 0](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:l](BlockMatrix(Exp(z[i, l - i - 1:]), ZeroMatrix(n - 1 - i))),
                     Lamda[i:n - l](BlockMatrix(ZeroMatrix(i + 1), Exp(z[i + l]), ZeroMatrix(n - 1 - i - l)))))


@prove
def prove(Eq):
    from axiom import patent, algebra, keras

    n, k = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    V = Symbol(shape=(n, n), real=True)
    z, V_quote = Symbol(shape=(n, l), real=True)
    r = Symbol(shape=(n,), integer=True)
    w = Symbol(shape=(k * 2 + 1,), integer=True)
    i, j = Symbol(integer=True)
    Eq << apply(
        Equal(V, Lamda[j:n, i:n]((w[k + clip(r[j] - r[i], -k, k)]))),
        Equal(V_quote, Lamda[j:l, i:n](w[k + clip(r[Min(n - 1, relu(i - l + 1) + j)] - r[i], -k, k)])),
        Equal(z, BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1] + V_quote[i, :i + 1])),
            V_quote[l:] + Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) - Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1] + V_quote[i, :Min(i + 1, l)]))))

    Eq << patent.eq_block.eq_block.imply.all_eq.relative_distance.lower_triangle.upper_part.apply(Eq[0], Eq[1])

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1].this.expr.reversed, Eq[2].find(Lamda).expr)

    Eq << patent.eq_block.eq_block.imply.all_eq.relative_distance.lower_triangle.lower_part.apply(Eq[0], Eq[1])

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1].this.expr.reversed)

    Eq << patent.eq_block.eq_block.imply.eq.relative_distance.lower_triangle.apply(Eq[0], Eq[1])

    Eq << Eq[2].subs(Eq[-1].reversed, Eq[-2], Eq[-4])

    Eq << Eq[-1].this.find(Lamda + Lamda).apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.find(-~Min).apply(keras.min.to.add.relu, index=0)

    A_quote = Symbol(A + V)
    Eq.A_quote_def = A_quote.this.definition

    Eq << Eq.A_quote_def[i][:i + 1]

    Eq << Eq.A_quote_def[i + l][i + 1:i + l + 1]

    Eq << Eq.A_quote_def[i][relu(i + 1 - l):i + 1]

    Eq << Eq[-4].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[-3].reversed)

    Eq << patent.eq_block.imply.eq.softmax.lower_triangle.st.logsumexp.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.A_quote_def)




if __name__ == '__main__':
    run()
# created on 2022-03-17
# updated on 2022-03-29
from . import tf
