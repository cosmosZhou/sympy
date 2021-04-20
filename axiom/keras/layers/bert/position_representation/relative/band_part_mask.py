from axiom.utility import prove, apply
from tensorflow.nn import softmax
from sympy import *
import tensorflow as tf
from axiom import keras, algebra, sets


@apply
def apply(seq_length, dx, dz, k, num_lower, num_upper):
    x = Symbol.x(shape=(seq_length, dx), real=True)
    W_Q = Symbol("W^Q", shape=(dx, dz), real=True)
    W_K = Symbol("W^K", shape=(dx, dz), real=True)
    W_V = Symbol("W^V", shape=(dx, dz), real=True)
    
    Q = Symbol.Q(x @ W_Q)
    K = Symbol.K(x @ W_K)
    V = Symbol.V(x @ W_V)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    w_K = Symbol("w^K", shape=(2 * k + 1, dz), real=True)
    w_V = Symbol("w^V", shape=(2 * k + 1, dz), real=True)
    
    a_K = Symbol("a^K", LAMBDA[j:seq_length, i:seq_length](w_K[k + tf.clip(j - i, -k, k)]))
    a_V = Symbol("a^V", LAMBDA[j:seq_length, i:seq_length](w_V[k + tf.clip(j - i, -k, k)]))
    
    a = Symbol.a(Q @ (K + a_K).T / sqrt(dz))
    
    a_quote = Symbol("a'", a - (1 - tf.linalg.band_part[num_lower, num_upper](OneMatrix(seq_length, seq_length))) * oo)
    
    s = Symbol.s(softmax(a_quote))
    
    z = Symbol.z(s @ (V + a_V))
    
    gram_width = num_lower + num_upper + 1
    start = i - num_lower
    stop = start + gram_width  # i + k_max + 1
    
    a_K_quote = Symbol("a^K'", LAMBDA[j:Min(seq_length, gram_width), i:seq_length](w_K[k + tf.clip(j - Min(i, num_lower), -k, k)]))
    a_V_quote = Symbol("a^V'", LAMBDA[j:Min(seq_length, gram_width), i:seq_length](w_V[k + tf.clip(j - Min(i, num_lower), -k, k)]))
    
    β = Symbol.beta(LAMBDA[i:seq_length](tf.nn.relu(start)))
            
    ζ = Symbol.zeta(LAMBDA[i:seq_length](Min(stop, seq_length)))
    
    indices = slice(β[i], ζ[i])
    indices0 = slice(0, ζ[i] - β[i])
    
    return Equal(z[i], softmax(Q[i] @ (K[indices] + a_K_quote[i][indices0]).T / sqrt(dz)) @ (V[indices] + a_V_quote[i][indices0]))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True, positive=True)
    
    l = Symbol.l(integer=True, positive=True)
    u = Symbol.u(integer=True, positive=True)
    dx = Symbol.d_x(integer=True, positive=True)
    dz = Symbol.d_z(integer=True, positive=True)

    Eq << apply(n, dx, dz, k, l, u)

    Eq << Eq[11].this.find(Min).apply(algebra.min.to.add.relu, swap=True)
    
    Eq << Eq[12].this.find(Min).apply(algebra.min.to.add.relu, swap=True)
    
    Eq <<= Eq[-2].subs(Eq[9].reversed), Eq[-1].subs(Eq[9].reversed)

    β = Eq[9].lhs.base
    ζ = Eq[10].lhs.base
    i, j = Eq[2].lhs.indices
        
    Eq <<= Eq[2].subs(j, j + β[i]), Eq[7].subs(j, j + β[i])
    
    Eq <<= algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq[-2]), algebra.eq.eq.imply.eq.transit.apply(Eq[-3], Eq[-1])
    
    gram_width = l + u + 1 
    Eq.K_equality = algebra.eq.imply.eq.lamda.apply(Eq[-2], (j, 0, Min(n, gram_width)))
    
    Eq.V_equality = algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, Min(n, gram_width)))

    Eq.le = LessEqual(ζ[i], β[i] + Min(n, l + u + 1), plausible=True)
    
    Eq << Eq.le.this.lhs.definition
    
    Eq << Eq[-1].this.rhs.args[0].definition.reversed
    
    Eq << keras.nn.relu.min.ge.apply(i + u + 1, l + u + 1, n)
     
    Eq.le = Eq.le - β[i]
    
    Eq << algebra.le.eq.imply.eq.slice.apply(Eq.le, Eq.K_equality)
    
    Eq << algebra.le.eq.imply.eq.slice.apply(Eq.le, Eq.V_equality)
    
    Eq.objective = Eq[13].subs(Eq[-1], Eq[-2])    
    
    a = Eq[3].lhs    
    band_part = Eq[4].rhs.args[1].args[1].args[1].args[1]
    Eq << keras.layers.bert.mask.theorem.apply(a, band_part)
    
    Eq << Eq[-1].subs(Eq[4].reversed)

    Ξ = Symbol.Ξ(band_part)
    
    Eq.Ξ_definition = Ξ.this.definition
    
    Eq << Eq[-1].subs(Eq.Ξ_definition.reversed)
    
    Eq << Eq[-1][i]
    Eq << Eq[8][i]
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq.z_definition = Eq[-1].this.rhs.subs(Eq[-3])
    
    Eq << Eq.Ξ_definition.this.rhs.definition
    
    Eq << Eq[-1][i]
    
    Eq.Ξ_definition = Eq[-1].this.rhs.function.definition
    
    Eq << Eq.z_definition.rhs.args[-1].args[0].this.arg.args[0].subs(Eq.Ξ_definition)
    
    Eq << Eq[-1].this.rhs.astype(Sum)
    
    Eq << Eq[-1].this.rhs.function.args[0].cond.apply(sets.contains.to.contains)
    
    Eq.start_definition = Eq[9].this.rhs.definition
    
    Eq.stop_definition = (Eq[10] - 1).this.rhs.astype(Min)
    
    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq.stop_definition.reversed)
    
    Eq << Eq[-1].this.rhs.astype(ReducedSum)
    
    Eq.z_definition = Eq.z_definition.subs(Eq[-1])
    
    Eq << Eq[3][i]
    
    Eq << Eq[-1][β[i]:ζ[i]]

    Eq << Eq.objective.this.rhs.subs(Eq[-1].reversed)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq.z_definition.rhs.args[0].this.expand()
    
    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined.insert)
    
    k = Eq[-1].rhs.function.variable
    Eq << Eq.Ξ_definition[k]
    
    Eq << Eq[-2].this.rhs.function.function.subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq.start_definition.reversed, Eq.stop_definition.reversed)
    
    Eq << Eq[-1].this.rhs.function.astype(MatMul)
    
    Eq << Eq[-1].this.rhs.function.T
    
    Eq << Eq[-1].this.rhs.function.args[1].astype(Add)
    
    Eq << Eq[-1].this.rhs.astype(MatMul)
    
    Eq << Eq.z_definition.this.rhs.subs(Eq[-1])

    
if __name__ == '__main__':
    prove()
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
