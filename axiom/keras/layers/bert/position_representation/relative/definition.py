from util import *


@apply
def apply(n, dx, dz):
    x = Symbol.x(shape=(n, dx), real=True)
    W_Q = Symbol("W^Q", shape=(dx, dz), real=True)
    W_K = Symbol("W^K", shape=(dx, dz), real=True)
    W_V = Symbol("W^V", shape=(dx, dz), real=True)

    Q = Symbol.Q(x @ W_Q)
    K = Symbol.K(x @ W_K)
    V = Symbol.V(x @ W_V)

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    k = Symbol.k(integer=True, positive=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, dz), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, dz), real=True)

    a_K = Symbol("a^K", Lamda[j:n, i:n](w_K[k + clip(j - i, -k, k)]))
    a_V = Symbol("a^V", Lamda[j:n, i:n](w_V[k + clip(j - i, -k, k)]))

    a = Symbol.a(Q @ (K + a_K).T / sqrt(dz))
    s = Symbol.s(softmax(a))

    z = Symbol.z(s @ (V + a_V))

    return Contains(k + clip(j - i, -k, k), Range(0, 2 * k + 1)), \
        Equal(a[i, j], (x[i] @ W_Q @ (x[j] @ W_K + a_K[i, j])) / sqrt(dz)), \
        Equal(z[i], Sum[j:n](s[i, j] * (x[j] @ W_V + a_V[i, j])))


@prove
def prove(Eq):
    from axiom import algebra, discrete
    n = Symbol.n(integer=True, positive=True)
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

    k = Symbol.k(integer=True)
    Eq << Eq[-1].this.rhs.args[0].apply(discrete.matmul.to.lamda, var={k})

    Eq << Eq[-1].this.rhs.args[-1].apply(algebra.lamda.to.sum)

    Eq << Eq[-1].this.rhs.subs(Eq[5][j])

    Eq << Eq[-1].this.rhs.args[0].apply(discrete.matmul.to.lamda, var={k})

    Eq << Eq[-1].this.rhs.args[0].apply(algebra.lamda.to.sum)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.sum)

    α = Eq[4].lhs
    Eq << Eq[-1].this.rhs.function.collect(α[i, j])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.domain_defined.insert)

    Eq << Eq[8].this.lhs.args[1].defun()

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.min)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.add.to.max)


if __name__ == '__main__':
    run()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
