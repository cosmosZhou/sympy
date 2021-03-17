from sympy import *
from axiom.utility import prove, apply
from axiom import keras, algebre
import axiom


@apply
def apply(a, Ξ):
    assert a.shape == Ξ.shape
    if Ξ.is_LAMBDA:
        function, *limits = axiom.is_LAMBDA(Ξ)
    else:        
        function, *limits = axiom.is_LAMBDA(Ξ.definition)
        
    assert function.is_Boole
    return Equality(exp(a - (1 - Ξ) * oo), Ξ * exp(a))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    p = Function.p(nargs=(2,), integer=True, shape=())    
    a = Symbol.a(real=True, shape=(n, n))
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    Ξ = Symbol.Ξ(LAMBDA[j:n, i:n](Boole(p(i, j) > 0)))
    Eq << apply(a, Ξ)
    
    a_quote = Symbol.a(a - (1 - Ξ) * oo)
    Eq << a_quote.this.definition
    
    Eq << Eq[-1][i, j]
    
    Eq << Eq[-1].this.rhs.args[1].args[1].args[1].args[1].definition
    
    Eq << Eq[-1].this.rhs.args[1].args[1].args[1].apply(algebre.bool.astype.piecewise, simplify=None)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << algebre.eq.imply.eq.exp.apply(Eq[-1])
    
    Eq.exp_a = Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << Eq[0].this.rhs.astype(Piecewise)
    
    Eq << Eq[-1] * exp(a[i, j])
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)

    Eq << algebre.eq.eq.imply.eq.transit.apply(Eq.exp_a, Eq[-1])
    
    Eq << algebre.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))
    
    Eq << Eq[-1].this.lhs.arg.definition

        
if __name__ == '__main__':
    prove(__file__)
# reference:
# Self-Attention with Relative Position Representations.pdf
# https://arxiv.org/abs/1803.02155
