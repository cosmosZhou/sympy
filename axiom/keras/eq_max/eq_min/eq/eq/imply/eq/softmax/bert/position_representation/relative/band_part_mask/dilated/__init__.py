from util import *


@apply
def apply(eq_max, eq_min, eq_K, eq_V, Q, K, V):
    ((((i, l), d), S[i - l + 1]), i_limit), β = eq_max.of(Equal[Lamda[Max[Mod[Expr + 1 - Expr]]]])
    S[i], S[0], n = i_limit

    (((S[i], u), S[n]), S[i_limit]), ζ = eq_min.of(Equal[Lamda[Min[Add]]])

    ((K_quote, S[i], j_index), j_limit, S[i_limit]), K_dquote = eq_K.of(Equal[Lamda[Indexed]])
    ((V_quote, S[i], S[j_index]), S[j_limit], S[i_limit]), V_dquote = eq_V.of(Equal[Lamda[Indexed]])
    j, S[0], S[Min(n, l + u - 1)] = j_limit
    (S[j], S[β[i]]), S[n - 1] = j_index.of(Min[Add])

    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i], d)
    indices0 = slice(0, ζ[i] - β[i], d)
    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1, d](OneMatrix(n, n)) - 1) * oo) @ (V + V_quote), \
                 Lamda[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets, discrete

    n, l, u, d = Symbol(integer=True, positive=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    K_quote = Symbol(shape=(n, n, d_z), real=True)
    V_quote = Symbol(shape=(n, n, d_z), real=True)
    β, ζ = Symbol(shape=(n,), integer=True)
    i, j = Symbol(integer=True)
    K_dquote = Symbol('K^\"', shape=(n, Min(n, l + u - 1), d_z))
    V_dquote = Symbol('V^\"', shape=(n, Min(n, l + u - 1), d_z))
    (Eq.beta, Eq.zeta, Eq.K_dquote, Eq.V_dquote), Eq.objective = apply(
        Equal(β, Lamda[i:n](Max(i - l + 1, (i - l + 1) % d))),
        Equal(ζ, Lamda[i:n](Min(i + u, n))),
        Equal(K_dquote, Lamda[j:Min(n, l + u - 1), i:n](K_quote[i, Min(n - 1, j + β[i])])),
        Equal(V_dquote, Lamda[j:Min(n, l + u - 1), i:n](V_quote[i, Min(n - 1, j + β[i])])),
        Q=Q, K=K, V=V)

    band_part = Eq.objective.find(BandPart)
    a = Symbol(Eq.objective.find(Mul[MatMul]))
    Eq << a.this.definition

    z = Symbol(Eq.objective.lhs)
    Eq << z.this.definition

    Eq.z_definition = Eq[-1].subs(Eq[0].reversed)

    Eq << keras.imply.eq.bert.mask.theorem.apply(a, band_part, add=True)

    a_quote = Symbol(Eq[-1].lhs.arg)
    Eq << Eq[-1].subs(a_quote.this.definition.reversed)

    Xi = Symbol(band_part)
    Eq.Xi_definition = Xi.this.definition

    i = Eq.beta.rhs.variable
    Eq << Eq[-1].subs(Eq.Xi_definition.reversed)[i]

    Eq << Eq.z_definition.subs(a_quote.this.definition.reversed)[i]

    Eq << Eq[-1].this.rhs.args[0].apply(keras.softmax.to.mul.reducedSum)

    Eq.zi_definition = Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Eq.Xi_definition.this.rhs.defun()[i]

    Eq.Xi_definition = Eq[-1].this.rhs.expr.apply(algebra.bool.to.piece)

    Eq << Eq.zi_definition.rhs.args[-1].args[0].this.arg.args[0].subs(Eq.Xi_definition)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Element).apply(sets.el.add, i)

    Eq.zeta_i = Eq.zeta[i]

    Eq << Eq[-1].subs(Eq.beta[i].reversed, Eq.zeta_i.reversed)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.rhs.args[0].this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined.insert)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_definition[k]

    Eq << Eq[-2].this.rhs.expr.expr.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.beta[i].reversed, Eq.zeta_i.reversed)

    Eq << Eq[-1].this.rhs.expr.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq.zi_definition.subs(Eq[-1])

    Eq << Eq[-1].this.find(Exp).apply(keras.exp.to.mul.softmax)

    Eq << Eq[0][i]

    Eq.le_zeta_i = algebra.eq.imply.le.relax.apply(Eq.zeta_i, upper=n)

    Eq << algebra.le.eq.imply.eq.slice.apply(Eq.le_zeta_i, Eq[-1], start=β[i], step=d)

    Eq.zi_definition = Eq[-3].subs(Eq[-1])

    Eq.le = algebra.eq_max.eq_min.imply.le.apply(Eq.beta, Eq.zeta)

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq.le, Eq.K_dquote[i], step=d), algebra.le.eq.imply.eq.slice.apply(Eq.le, Eq.V_dquote[i], step=d)

    Eq <<= Eq[-2].this.find(Min[~Add]).apply(algebra.expr.to.piece, upper=ζ[i] - 1), Eq[-1].this.find(Min[~Add]).apply(algebra.expr.to.piece, upper=ζ[i] - 1)

    Eq <<= Eq[-2].this.rhs().find(GreaterEqual).simplify(), Eq[-1].this.rhs().find(GreaterEqual).simplify()

    Eq <<= Eq[-2].this.find(Min).args[1].apply(algebra.expr.to.piece, lower=ζ[i] - 1), Eq[-1].this.find(Min).args[1].apply(algebra.expr.to.piece, lower=ζ[i] - 1)

    Eq <<= algebra.cond.cond.imply.cond.subs.apply(Eq.le_zeta_i, Eq[-2]), algebra.cond.cond.imply.cond.subs.apply(Eq.le_zeta_i, Eq[-1])

    Eq <<= Eq[-2].this.rhs().find(Min).simplify(), Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq.zi_definition.subs(Eq[-1].reversed, Eq[-2].reversed)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-12-26
# updated on 2022-03-30

from . import compact
