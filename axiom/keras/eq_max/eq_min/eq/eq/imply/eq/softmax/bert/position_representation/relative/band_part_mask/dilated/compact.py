from util import *


@apply
def apply(eq_max, eq_min, eq_K, eq_V, Q, K, V):
    ((((i, l), d), S[i - l + 1]), i_limit), β = eq_max.of(Equal[Lamda[Max[Mod[Expr + 1 - Expr]]]])
    S[i], S[0], n = i_limit

    (((S[i], u), S[n]), S[i_limit]), ζ = eq_min.of(Equal[Lamda[Min[Add]]])
    
    ((K_quote, S[i], j_index), j_limit, S[i_limit]), K_dquote = eq_K.of(Equal[Lamda[Indexed]])
    ((V_quote, S[i], S[j_index]), S[j_limit], S[i_limit]), V_dquote = eq_V.of(Equal[Lamda[Indexed]])
    j, (S[0], S[Min(n, l + u - 1)], S[d]) = j_limit.of(Tuple[Range])
    (S[j], S[β[i]]), S[n - 1] = j_index.of(Min[Add])

    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i], d)
    indices0 = slice(0, Ceiling((ζ[i] - β[i]) / d))

    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1, d](OneMatrix(n, n)) - 1) * oo) @ (V + V_quote), \
                 Lamda[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n, l, u, d = Symbol(integer=True, positive=True)
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    K_quote = Symbol(shape=(n, n, d_z), real=True)
    V_quote = Symbol(shape=(n, n, d_z), real=True)
    β, ζ = Symbol(shape=(n,), integer=True)
    i, j = Symbol(integer=True)
    K_dquote = Symbol('K^\"', shape=(n, Ceiling(Min(n, l + u - 1) / d), d_z))
    V_dquote = Symbol('V^\"', shape=(n, Ceiling(Min(n, l + u - 1) / d), d_z))
    (Eq.beta, Eq.zeta, Eq.K_dquote, Eq.V_dquote), Eq.objective = apply(
        Equal(β, Lamda[i:n](Max(i - l + 1, (i - l + 1) % d))),
        Equal(ζ, Lamda[i:n](Min(i + u, n))),
        Equal(K_dquote, Lamda[j:Range(0, Min(n, l + u - 1), d), i:n](K_quote[i, Min(n - 1, j + β[i])])),
        Equal(V_dquote, Lamda[j:Range(0, Min(n, l + u - 1), d), i:n](V_quote[i, Min(n - 1, j + β[i])])),
        Q=Q, K=K, V=V)

    Eq.le = algebra.eq_max.eq_min.imply.le.apply(Eq.beta, Eq.zeta)

    K_dquote = Symbol('K^\"', Lamda[j:Min(n, l + u - 1), i:n](K_quote[i, Min(n - 1, j + β[i])]))
    V_dquote = Symbol('V^\"', Lamda[j:Min(n, l + u - 1), i:n](V_quote[i, Min(n - 1, j + β[i])]))
    Eq <<= K_dquote.this.definition, V_dquote.this.definition

    Eq <<= Eq[-2][i], Eq[-1][i]

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq.le, Eq[-2], step=d), algebra.le.eq.imply.eq.slice.apply(Eq.le, Eq[-1], step=d)

    Eq.eq_K_dquote = Eq[-2].this.rhs.apply(algebra.lamda.range.simplify)

    Eq.eq_V_dquote = Eq[-1].this.rhs.apply(algebra.lamda.range.simplify)

    Eq <<= Eq.K_dquote[i], Eq.V_dquote[i]

    Eq << algebra.le.imply.le.ceiling.apply(Eq.le / d)

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq[-1], Eq[-3]), algebra.le.eq.imply.eq.slice.apply(Eq[-1], Eq[-2])

    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq.eq_K_dquote, Eq[-2]), algebra.eq.eq.imply.eq.transit.apply(Eq.eq_V_dquote, Eq[-1])

    Eq << keras.eq_max.eq_min.eq.eq.imply.eq.softmax.bert.position_representation.relative.band_part_mask.dilated.apply(Eq.beta, Eq.zeta, Eq[0], Eq[1], Q, K, V)

    Eq << Eq[-1].subs(Eq[-3], Eq[-2])

    
    


if __name__ == '__main__':
    run()

# created on 2021-12-26
# updated on 2022-03-30
