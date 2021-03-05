from axiom.utility import prove, apply
from tensorflow.nn import softmax
from sympy import *
from axiom import keras, algebre


@apply
def apply(n, dz, h):    
    Q = Symbol.Q(shape=(n, dz), real=True)
    K = Symbol.K(shape=(n, dz), real=True)
    V = Symbol.V(shape=(n, dz), real=True)
    
    a = Symbol.a(Q @ K.T / sqrt(dz))
    
    Ξ = Symbol.Ξ(Identity(n) + BlockMatrix([[ZeroMatrix(h, h), OneMatrix(h, n - h)],
                                                       [OneMatrix(n - h, h), ZeroMatrix(n - h, n - h)]]))
    
    a_quote = Symbol("a'", a - (1 - Ξ) * oo)
    
    s = Symbol.s(softmax(a_quote))
    
    z = Symbol.z(s @ V)
    
    # diagonal part
    D = Symbol.D((exp(ReducedSum(Q * K) / sqrt(dz)) * OneMatrix(dz, n)).T)
    
    # upper part
    Wu = Symbol("W^u", exp(Q[:h] @ K[h:n].T / sqrt(dz)))
    Vu = Symbol("V^u", V[:h])
    Du = Symbol("D^u", D[:h])
        
    # lower part
    Wl = Symbol("W^l", exp(Q[h:n] @ K[:h].T / sqrt(dz)))    
    Vl = Symbol("V^l", V[h:n])
    Dl = Symbol("D^l", D[h:n])

    return Equality(z, BlockMatrix((Wu @ Vl + Du * Vu) / (ReducedSum(Wu) + Du), (Wl @ Vu + Dl * Vl) / (ReducedSum(Wl) + Dl)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    h = Symbol.h(domain=Interval(1, n - 1, integer=True))
    dz = Symbol.d_z(integer=True, positive=True)

    Eq << apply(n, dz, h)
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))    
    j = Symbol.j(integer=True)
    
    a = Eq[0].lhs
    Eq << keras.layers.bert.mask.cross_attention.apply(a, h)

    Eq.ai_definition = Eq[-1][i]
    
    Eq << Eq[4][i]
    
    Eq.z_definition = Eq[-1].this.rhs.args[0].definition

    Eq.z_definition = Eq.z_definition.this.rhs.subs(Eq[-1])
         
    Eq.z_definition = Eq.z_definition.this.rhs.subs(Eq.ai_definition)
    
    Eq << Eq.z_definition.rhs.args[-1].args[0].this.astype(MatMul)

    Eq << Eq[-1].this.rhs.expand()
     
    Eq << Eq[-1].this.rhs.subs(Eq[1][i, j])
    
    Eq << Eq[-1].this.rhs.args[0]().expr.args[0].simplify()
    
    Eq << Eq[-1].this.rhs.args[-1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0]().expr.args[1]().function.simplify()
    
    Eq << Eq[-1].this.rhs.args[1]().expr.args[1]().function.simplify()
    
    Eq << Eq[-1].this.rhs.simplify(wrt=True)

    Eq.divisor_definition = Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq.divisor_definition.rhs.args[0].args[-1].expr.this.astype(ReducedSum)
    
    Eq << Eq.divisor_definition.rhs.args[0].args[0].expr.this.astype(ReducedSum)
    
    Eq.divisor_definition = Eq.divisor_definition.this.rhs.subs(Eq[-2], Eq[-1], simplify=False)
    
    Eq << Eq[5][i]
    
    Eq << Eq[-1].this.rhs.args[1].arg.args[1].astype(MatMul)
    
    Eq.M_definition = Eq[-1].this.rhs.args[1].arg.args[1].T
    
    Eq << Eq[0][i]
    
    Eq <<= Eq[-1][h:n], Eq[-1][:h], Eq[-1][i]
    
    Eq <<= algebre.equal.imply.equal.exp.apply(Eq[-3]), algebre.equal.imply.equal.exp.apply(Eq[-2]), algebre.equal.imply.equal.exp.apply(Eq[-1])
    
    Eq << Eq[-1] * OneMatrix(dz)

    Eq.lower_part, Eq.upper_part, Eq.diagonal_part = algebre.equal.equal.imply.equal.transit.apply(Eq[-4], Eq[7][i]), \
        algebre.equal.equal.imply.equal.transit.apply(Eq[-3], Eq[11][i - h]), \
        algebre.equal.equal.imply.equal.transit.apply(Eq[-1], Eq.M_definition)
        
    Eq << Eq.divisor_definition * OneMatrix(dz)
    
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq[-1].this.rhs.subs(Eq.lower_part, Eq.upper_part, Eq.diagonal_part)
    
    Eq.z_definition = algebre.equal.condition.imply.condition.subs_with_expand_dims.apply(Eq[-1], Eq.z_definition)
    
    Eq << Eq.z_definition.rhs.args[0].this.expand()
    
    Eq << Eq[-1].this.rhs.function.function.args[1].definition
    
    Eq << Eq[-1].this(i).rhs.function.args[0]().expr.simplify()
    
    Eq << Eq[-1].this.rhs.function.args[-1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.function.apply(algebre.piecewise.swap.back)
    
    Eq << Eq[-1].this.rhs.function.simplify(wrt=i)
    
    Eq << Eq[-1].this.rhs.function.astype(Plus)
    
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].function.args[0].expr.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].function.args[0]().expr.args[1].simplify()
    
    Eq << Eq[-1].this.rhs.args[1].function.args[1].expr.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].function.args[1]().expr.args[1].simplify()
    
    Eq << Eq[-1].this.rhs.args[1].function.args[0].expr.astype(MatMul)
    
    Eq << Eq[-1].this.rhs.args[1].function.args[1].expr.astype(MatMul)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].args[0].expr.astype(MatMul)
    
    Eq << Eq[-1].this.rhs.args[1].args[0].expr.T
    
    Eq << Eq[-1].this.rhs.args[1].args[1].expr.astype(MatMul)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].expr.T
    
    Eq << Eq[-1].this.rhs.subs(Eq.lower_part, Eq.upper_part)
    
    Eq << algebre.equal.condition.imply.condition.subs_with_expand_dims.apply(Eq.diagonal_part, Eq[-1])
    
    Eq << Eq.z_definition.this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.args[0].args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (i,))
    
    Eq << Eq[-1].this.rhs.astype(BlockMatrix)
    
    Eq << Eq[-1].this.rhs.args[0].astype(Times)
    
    Eq << Eq[-1].this.rhs.args[0].args[0].astype(Power)

    Eq << Eq[-1].this.rhs.args[1].astype(Times)
    
    Eq << Eq[-1].this.rhs.args[1].args[0].astype(Power)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].base.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].base.args[1].astype(ReducedSum)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].base.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].base.args[1].astype(ReducedSum)
    
    Eq << Eq[-1].this.rhs.subs(Eq[6].reversed, Eq[8].reversed, Eq[9].reversed, Eq[10].reversed)

        
if __name__ == '__main__':
    prove(__file__)
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
