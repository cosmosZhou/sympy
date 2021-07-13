from util import *


@apply
def apply(seq_length, dx, dz, num_lower, num_upper):
    x = Symbol.x(shape=(seq_length, dx), real=True)
    W_Q = Symbol("W^Q", shape=(dx, dz), real=True)
    W_K = Symbol("W^K", shape=(dx, dz), real=True)
    W_V = Symbol("W^V", shape=(dx, dz), real=True)

    Q = Symbol.Q(x @ W_Q)
    K = Symbol.K(x @ W_K)
    V = Symbol.V(x @ W_V)

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)

    a = Symbol.a(Q @ K.T / sqrt(dz))

    a_quote = Symbol("a'", a - (1 - linalg.band_part[num_lower, num_upper](OneMatrix(seq_length, seq_length))) * oo)

    s = Symbol.s(softmax(a_quote))

    z = Symbol.z(s @ V)

    gram_width = num_lower + num_upper + 1
    start = i - num_lower
    stop = start + gram_width  # i + k_max + 1

    beta = Symbol.beta(Lamda[i:seq_length](relu(start)))

    zeta = Symbol.zeta(Lamda[i:seq_length](Min(stop, seq_length)))

    assert beta.is_integer and zeta.is_integer
    indices = slice(beta[i], zeta[i])    

    return Equal(z[i], softmax(Q[i] @ (K[indices]).T / sqrt(dz)) @ (V[indices]))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets, discrete

    n = Symbol.n(integer=True, positive=True)
    l = Symbol.l(integer=True, positive=True)
    u = Symbol.u(integer=True, positive=True)
    dx = Symbol.d_x(integer=True, positive=True)
    dz = Symbol.d_z(integer=True, positive=True)
    Eq << apply(n, dx, dz, l, u)

    beta = Eq[7].lhs.base
    zeta = Eq[8].lhs.base
    i = Eq[-1].lhs.index
    Eq.le = LessEqual(zeta[i], beta[i] + Min(n, l + u + 1), plausible=True)

    Eq << Eq.le.this.lhs.definition

    Eq << Eq[-1].this.rhs.args[0].definition.reversed

    Eq << keras.nn.relu.min.ge.apply(i + u + 1, l + u + 1, n)

    Eq.le = Eq.le - beta[i]

    a = Eq[2].lhs
    band_part = Eq[3].find(BandPart)
    Eq << keras.layers.bert.mask.theorem.apply(a, band_part)

    Eq << Eq[-1].subs(Eq[3].reversed)

    Xi = Symbol.Xi(band_part)
    Eq.Xi_definition = Xi.this.definition

    Eq << Eq[-1].subs(Eq.Xi_definition.reversed)

    Eq << Eq[-1][i]

    Eq << Eq[6][i]

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq.z_definition = Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Eq.Xi_definition.this.rhs.defun()

    Eq << Eq[-1][i]

    Eq.Xi_definition = Eq[-1].this.rhs.function.apply(algebra.bool.to.piecewise)

    Eq << Eq.z_definition.rhs.args[-1].args[0].this.arg.args[0].subs(Eq.Xi_definition)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Contains).apply(sets.contains.negate)

    Eq.start_definition = Eq[7].this.rhs.defun()

    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq[8].reversed)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    Eq.z_definition = Eq.z_definition.subs(Eq[-1])

    Eq << Eq[2][i]

    Eq << Eq[-1][beta[i]:zeta[i]]

    Eq << Eq[9].this.rhs.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(softmax).apply(keras.softmax.to.mul)

    Eq << Eq.z_definition.rhs.args[0].this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined.insert)

    k = Eq[-1].rhs.function.variable
    Eq << Eq.Xi_definition[k]

    Eq << Eq[-2].this.rhs.function.function.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq[8].reversed)

    Eq << Eq[-1].this.rhs.function.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.rhs.function.T

    

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq.z_definition.this.rhs.subs(Eq[-1])


if __name__ == '__main__':
    run()