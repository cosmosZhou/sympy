from axiom.utility import prove, apply
from sympy import *

from axiom import keras, algebre

@apply
def apply(a, h):    
    n = a.shape[0]
    Ξ = Symbol.Ξ(Identity(n) + BlockMatrix([[ZeroMatrix(h, h), OneMatrix(h, n - h)],
                                                       [OneMatrix(n - h, h), ZeroMatrix(n - h, n - h)]]))
    
    a_quote = Symbol("a'", a - (1 - Ξ) * oo)
    
    return Equality(exp(a_quote), Ξ * exp(a))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)    
    h = Symbol.h(domain=Interval(1, n - 1, integer=True))
    dz = Symbol.d_z(integer=True, positive=True)
    Q = Symbol.Q(shape=(n, dz), real=True)
    K = Symbol.K(shape=(n, dz), real=True)
#     a = Symbol.a(Q @ K.T / sqrt(dz))
    a = Symbol.a(shape=(n, n), real=True)
    dz = Symbol.d_z(integer=True, positive=True)

    Eq << apply(a, h)
    
    i = Symbol.i(integer=True)    
    j = Symbol.j(integer=True)
    
    Ξ_quote = Symbol("Ξ'", LAMBDA[j:n, i:n](Boole(Equality(i, j) | (i < h) & (j >= h) | (i >= h) & (j < h))))
    
    Eq << Ξ_quote[i, j].this.definition
    
    Eq.Ξ_quote_definition = Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[0][i, j]
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[0]().expr.args[1]().expr.simplify()
    
    Eq.Ξ_definition = Eq[-1].this.rhs.args[1]().expr.simplify()
    
    Eq << Eq.Ξ_definition.this.rhs.args[-1].expr.astype(Piecewise)

    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.flatten)
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.flatten, index=0)    
    
    Eq << Eq[-1].this.rhs.args[0].expr.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.swap.back)
    
    Eq << Eq[-1].this.rhs.args[1].cond.collect(i < h)
    
    Eq << Eq[-1].this.rhs.args[1].cond.collect(j < h)
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.swap.back)
    
    Eq << Eq[-1].this.rhs.args[0].cond.collect(Equality(i, j))
    
    Eq << Eq[-1].this.rhs.args[0].cond.args[0].args[0].astype(Or)
    
    Eq << Eq[-1].this.rhs.args[0].cond.args[1].args[1].reversed
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.Ξ_quote_definition, Eq[-1])
    
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))

    a = Eq[1].rhs.args[0]
    Eq << keras.layers.bert.mask.theorem.apply(a, Ξ_quote)
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq[-1].subs(Eq[1].reversed)
        
if __name__ == '__main__':
    prove(__file__)
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
