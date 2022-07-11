from util import *


@apply
def apply(eq_max, eq_min, Q, K, V):    
    ((((i, l), d), S[i - l + 1]), i_limit), β = eq_max.of(Equal[Lamda[Max[Mod[Expr + 1 - Expr]]]])
    S[i], S[0], n = i_limit

    (((S[i], u), S[n]), S[i_limit]), ζ = eq_min.of(Equal[Lamda[Min[Add]]])
    
    S[n], d_z = Q.shape

    indices = slice(β[i], ζ[i], d)

    return Equal(softmax(Q @ K.T / sqrt(d_z) + (BandPart[l - 1, u - 1, d](OneMatrix(n, n)) - 1) * oo) @ V, Lamda[i:n](softmax(Q[i] @ (K[indices]).T / sqrt(d_z)) @ (V[indices])))


@prove
def prove(Eq):
    from axiom import keras

    n, l, u, d_z, d = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Q = Symbol(real=True, shape=(n, d_z))
    K = Symbol(real=True, shape=(n, d_z))
    V = Symbol(real=True, shape=(n, d_z))
    β, ζ = Symbol(shape=(n,), integer=True)
    (Eq.beta, Eq.zeta), Eq.objective = apply(Equal(β, Lamda[i:n](Max(i - l + 1, (i - l + 1) % d))), Equal(ζ, Lamda[i:n](Min(i + u, n))), Q, K, V)

    A = Symbol(Eq.objective.find(Mul[MatMul]))
    Eq << keras.eq_max.eq_min.imply.eq.matmul.softmax.band_part_mask.dilated.apply(Eq.beta, Eq.zeta, A, V)

    Eq << Eq[-1].subs(A.this.definition)

    
    


if __name__ == '__main__':
    run()
# created on 2022-01-01
# updated on 2022-03-30
