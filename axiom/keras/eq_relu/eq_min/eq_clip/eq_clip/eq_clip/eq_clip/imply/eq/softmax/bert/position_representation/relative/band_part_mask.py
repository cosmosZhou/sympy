from util import *


@apply
def apply(eq_relu, eq_min, eq_K_quote, eq_V_quote, eq_K, eq_V, Q, K, V):
    ((i, l), i_limit), β = eq_relu.of(Equal[Lamda[relu[Expr + 1 - Expr]]])
    S[i], S[0], n = i_limit

    (((S[i], u), S[n]), S[i_limit]), ζ = eq_min.of(Equal[Lamda[Min[Add]]])    

    ((w_K, clip_index), j_limit, S[i_limit]), K_dquote = eq_K.of(Equal[Lamda[Indexed]])
    ((w_V, S[clip_index]), S[j_limit], S[i_limit]), V_dquote = eq_V.of(Equal[Lamda[Indexed]])
    j, S[0], S[Min(n, l + u - 1)] = j_limit
    k, (S[j - i + β[i]], S[-k], S[k]) = clip_index.of(Add[clip])

    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i])
    indices0 = slice(0, ζ[i] - β[i])

    ((S[w_K], clip_index), j_limit, S[i_limit]), K_quote = eq_K_quote.of(Equal[Lamda[Indexed]])
    ((S[w_V], S[clip_index]), S[j_limit], S[i_limit]), V_quote = eq_V_quote.of(Equal[Lamda[Indexed]])
    S[k], (S[j - i], S[-k], S[k]) = clip_index.of(Add[clip])
    S[j], S[0], S[n] = j_limit
    
    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo) @ (V + V_quote),
                 Lamda[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))



@prove
def prove(Eq):
    from axiom import keras, algebra

    n, k, l, u = Symbol(integer=True, positive=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    β, ζ = Symbol(shape=(n,), integer=True)
    w_K = Symbol("w^K", shape=(2 * k + 1, d_z), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, d_z), real=True)
    i, j = Symbol(integer=True)
    K_quote = Symbol(real=True, shape=(n, n, d_z))
    V_quote = Symbol(real=True, shape=(n, n, d_z))
    K_dquote = Symbol('K^\"', real=True, shape=(n, Min(n, l + u - 1), d_z))
    V_dquote = Symbol('V^\"', real=True, shape=(n, Min(n, l + u - 1), d_z))
    (Eq.beta, Eq.zeta, Eq.K_quote, Eq.V_quote, Eq.K_dquote, Eq.V_dquote), Eq.objective = apply(
        Equal(β, Lamda[i:n](relu(i - l + 1))),
        Equal(ζ, Lamda[i:n](Min(i + u, n))),
        Equal(K_quote, Lamda[j:n, i:n](w_K[k + clip(j - i, -k, k)])),
        Equal(V_quote, Lamda[j:n, i:n](w_V[k + clip(j - i, -k, k)])),
        Equal(K_dquote, Lamda[j:Min(n, l + u - 1), i:n](w_K[k + clip(j - i + β[i], -k, k)])),
        Equal(V_dquote, Lamda[j:Min(n, l + u - 1), i:n](w_V[k + clip(j - i + β[i], -k, k)])),
        Q, K, V)

    K_dquote = Symbol('K^\"', Transpose[1](Lamda[j:Min(n, l + u - 1)](K_quote[:, Min(n - 1, j + β[i])])))
    V_dquote = Symbol('V^\"', Transpose[1](Lamda[j:Min(n, l + u - 1)](V_quote[:, Min(n - 1, j + β[i])])))
    Eq <<= K_dquote.this.definition, V_dquote.this.definition

    Eq << keras.eq_relu.eq_min.eq.eq.imply.eq.softmax.bert.position_representation.relative.band_part_mask.apply(Eq.beta, Eq.zeta, Eq[-2], Eq[-1], Q, K, V)

    Eq <<= Eq[0][i], Eq[1][i]

    Eq.le_min = keras.eq_relu.eq_min.imply.le.apply(Eq.beta, Eq.zeta)

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq.le_min, Eq[-2]), algebra.le.eq.imply.eq.slice.apply(Eq.le_min, Eq[-1])

    Eq <<= Eq[-2].this.find(Min).args[0].apply(algebra.expr.to.piece, upper=ζ[i] - 1), Eq[-1].this.find(Min).args[0].apply(algebra.expr.to.piece, upper=ζ[i] - 1)

    Eq <<= Eq[-2].this.rhs().find(GreaterEqual).simplify(), Eq[-1].this.rhs().find(GreaterEqual).simplify()

    Eq <<= Eq[-2].this.find(Min).args[1].apply(algebra.expr.to.piece, lower=ζ[i] - 1), Eq[-1].this.find(Min).args[1].apply(algebra.expr.to.piece, lower=ζ[i] - 1)

    Eq.le_zeta = algebra.eq.imply.le.relax.apply(Eq.zeta[i], upper=n)

    Eq <<= algebra.cond.cond.imply.cond.subs.apply(Eq.le_zeta, Eq[-2]), algebra.cond.cond.imply.cond.subs.apply(Eq.le_zeta, Eq[-1])

    Eq <<= Eq[-2].this.rhs().find(Min).simplify(), Eq[-1].this.rhs().find(Min).simplify()

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq.le_zeta, Eq.K_quote[i], start=β[i]), algebra.le.eq.imply.eq.slice.apply(Eq.le_zeta, Eq.V_quote[i], start=β[i])

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq[-2]), algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq.le_min, Eq.K_dquote[i]), algebra.le.eq.imply.eq.slice.apply(Eq.le_min, Eq.V_dquote[i])

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq[-2]), algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])

    Eq << Eq[2].subs(Eq[-2], Eq[-1])

    
    


if __name__ == '__main__':
    run()

# created on 2020-12-30
# updated on 2022-03-30
