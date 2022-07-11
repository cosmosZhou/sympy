from util import *


@apply
def apply(eq_relu, eq_min, eq_K, eq_V, Q, K, V):
    ((i, l), i_limit), β = eq_relu.of(Equal[Lamda[relu[Expr + 1 - Expr]]])
    S[i], S[0], n = i_limit

    (((S[i], u), S[n]), S[i_limit]), ζ = eq_min.of(Equal[Lamda[Min[Add]]])

    ((K_quote, range_n, j_index), j_limit), K_dquote = eq_K.of(Equal[Transpose[1][Lamda[SlicedIndexed]]])
    ((V_quote, S[range_n], S[j_index]), S[j_limit]), V_dquote = eq_V.of(Equal[Transpose[1][Lamda[SlicedIndexed]]])

    S[0], S[n] = range_n
    j, S[0], S[Min(n, l + u - 1)] = j_limit
    (S[j], S[β[i]]), S[n - 1] = j_index.of(Min[Add])

    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i])
    indices0 = slice(0, ζ[i] - β[i])
    return Equal(softmax(Q @ (K + K_quote).T / sqrt(d_z) + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo) @ (V + V_quote), Lamda[i:n](softmax(Q[i] @ (K[indices] + K_dquote[i][indices0]).T / sqrt(d_z)) @ (V[indices] + V_dquote[i][indices0])))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets, discrete

    n, l, u = Symbol(integer=True, positive=True)
    #l denotes the size of the preceding context including current position;
    #u denotes the size of the subsequent context including current position;
    d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    V = Symbol(shape=(n, d_z), real=True)
    β, ζ = Symbol(shape=(n,), integer=True)
    i, j = Symbol(integer=True)
    K_quote = Symbol(shape=(n, n, d_z), real=True)
    V_quote = Symbol(shape=(n, n, d_z), real=True)
    K_dquote = Symbol('K^\"', real=True, shape=(n, Min(n, l + u - 1), d_z))
    V_dquote = Symbol('V^\"', real=True, shape=(n, Min(n, l + u - 1), d_z))
    (Eq.beta, Eq.zeta, Eq.K_dquote, Eq.V_dquote), Eq.objective = apply(Equal(β, Lamda[i:n](relu(i - l + 1))), \
                                                                       Equal(ζ, Lamda[i:n](Min(i + u, n))), \
                                                                       Equal(K_dquote, Transpose[1](Lamda[j:Min(n, l + u - 1)](K_quote[:, Min(n - 1, j + β[i])]))), \
                                                                       Equal(V_dquote, Transpose[1](Lamda[j:Min(n, l + u - 1)](V_quote[:, Min(n - 1, j + β[i])]))), Q, K, V)

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
    Eq.Xi_def = Xi.this.definition

    Eq << Eq[-1].subs(Eq.Xi_def.reversed)[i]

    Eq << Eq.z_definition.subs(a_quote.this.definition.reversed)[i]

    Eq << Eq[-1].this.find(softmax).apply(keras.softmax.to.mul.reducedSum)

    Eq.zi_definition = Eq[-1].this.rhs.subs(Eq[-3])

    Eq << Eq.Xi_def.this.rhs.defun()[i]

    Eq.Xi_def = Eq[-1].this.rhs.expr.apply(algebra.bool.to.piece)

    Eq << Eq.zi_definition.find(ReducedSum).this.subs(Eq.Xi_def)

    Eq << Eq[-1].this.rhs.apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.find(Element).apply(sets.el.add, i)

    Eq.start_definition = Eq.beta[i].this.rhs.defun()

    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq.zeta[i].reversed)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    Eq.zi_definition = Eq.zi_definition.subs(Eq[-1])

    Eq << Eq.zi_definition.find(MatMul).this.apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined.insert)

    k = Eq[-1].rhs.expr.variable
    Eq << Eq.Xi_def[k]

    Eq << Eq[-2].this.rhs.expr.expr.subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq.zeta[i].reversed)

    Eq << Eq[-1].this.rhs.expr.apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.rhs.expr.T

    Eq << Eq[-1].this.rhs.apply(discrete.lamda_matmul.to.matmul)

    Eq << Eq.zi_definition.subs(Eq[-1])

    Eq << Eq[-1].this.find(Exp).apply(keras.exp.to.mul.softmax)

    Eq << Eq[0][i]

    Eq.le_zeta_i = algebra.eq.imply.le.relax.apply(Eq.zeta[i], upper=n)

    Eq << algebra.le.eq.imply.eq.slice.apply(Eq.le_zeta_i, Eq[-1], start=β[i])

    Eq.zi_definition = Eq[-3].subs(Eq[-1])

    Eq << keras.eq_relu.eq_min.imply.le.apply(Eq.beta, Eq.zeta)

    Eq <<= algebra.le.eq.imply.eq.slice.apply(Eq[-1], Eq.K_dquote[i]), algebra.le.eq.imply.eq.slice.apply(Eq[-1], Eq.V_dquote[i])

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

# created on 2021-12-14
# updated on 2022-03-30
