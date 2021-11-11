from util import *


@apply
def apply(n, dx, dz):
    x = Symbol(shape=(n, dx), real=True)
    W_Q = Symbol("W^Q", shape=(dx, dz), real=True)
    W_K = Symbol("W^K", shape=(dx, dz), real=True)
    W_V = Symbol("W^V", shape=(dx, dz), real=True)

    Q = Symbol(x @ W_Q)
    K = Symbol(x @ W_K)
    V = Symbol(x @ W_V)

    i, j = Symbol(integer=True)

    k = Symbol(integer=True, positive=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, dz), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, dz), real=True)

    a_K = Symbol("a^K", Lamda[j:n, i:n](w_K[k + clip(j - i, -k, k)]))
    a_V = Symbol("a^V", Lamda[j:n, i:n](w_V[k + clip(j - i, -k, k)]))

    a = Symbol(Q @ (K + a_K).T / sqrt(dz))
    s = Symbol(softmax(a))

    z = Symbol(s @ (V + a_V))

    return Element(k + clip(j - i, -k, k), Range(2 * k + 1)), \
        Equal(a[i, j], (x[i] @ W_Q @ (x[j] @ W_K + a_K[i, j])) / sqrt(dz)), \
        Equal(z[i], Sum[j:n](s[i, j] * (x[j] @ W_V + a_V[i, j])))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    dx = Symbol.d_x(integer=True, positive=True)
    dz = Symbol.d_z(integer=True, positive=True)
    Eq << apply(n, dx, dz)

    i, j = Eq[2].lhs.indices
    Eq << Eq[-2].subs(Eq[0][i].reversed)

    Eq << Eq[-1].subs(Eq[1][j].reversed)

    Eq << Eq[3][i, j]

    Eq << Eq[4][i, j]

    Eq << Eq[7][i]

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.add)

    Eq << Eq[-1].this.rhs.args[0].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.args[-1].apply(algebra.lamda.to.sum)

    h = Eq[-1].find(Sum).variable
    Eq << Eq[-1].this.rhs.subs(Eq[5][h])

    Eq << Eq[-1].this.rhs.args[0].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.lamda.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.rhs.limits_subs(h, j)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[8].this.lhs.args[1].defun()

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.min)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.add.to.max)


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
# created on 2021-01-03
# updated on 2021-01-03
