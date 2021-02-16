from axiom.utility import prove, apply

from sympy import *
from axiom import algebre, sets

from tensorflow.nn.convolutional.same import conv1d


@apply(imply=True)
def apply(x, w, β, ζ):    
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m, n, d = x.shape
    M = Symbol.M(definition=LAMBDA[j:d, i:n, k:m](Boole((i >= β[k]) & (i < ζ[k]))))
    return Equality(conv1d(x * M, w) * M,
                    LAMBDA[k:m](BlockMatrix(ZeroMatrix(β[k], d), 
                                            conv1d(x[k][β[k]:ζ[k]], w), 
                                            ZeroMatrix(n - ζ[k], d))))


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    d = Symbol.d(integer=True, positive=True)
    l = Symbol.l(integer=True, positive=True)
    
    β = Symbol.β(shape=(m,), domain=Interval(0, n - 1, integer=True))
    ζ = Symbol.ζ(shape=(m,), domain=Interval(1, n, integer=True))
    x = Symbol.x(real=True, shape=(m, n, d))
    w = Symbol.w(real=True, shape=(l, d, d))
    
    Eq << apply(x, w, β, ζ)
    C = Symbol.C(definition=Eq[1].lhs)

    Eq << C.this.definition
    
    Eq << Eq[-1].this.rhs.args[1].definition
        
    k, i, j = Eq[0].lhs.indices
    
    Eq << Eq[-1][k, i]

    Eq << Eq[-1].this.rhs.args[1].function.args[0].args[0].definition
    
    Eq << Eq[-1].this.rhs.args[1].function.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][-1].args[1].astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[0].astype(Piecewise)
    
    Eq.convolution_definition = Eq[-1].this.rhs.astype(Piecewise)
    
    C_quote = Symbol("C'", definition=Eq[1].rhs)
    
    Eq << C_quote.this.definition
    
    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.args[1].definition
    
    Eq << Eq[-1][i]
    
    Eq << Eq[-1].this.rhs.apply(algebre.imply.equal.piecewise.swap.front)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits_subs(j, j - β[k])
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][1].astype(Max)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][2].astype(Min)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.convolution_definition, Eq[-1])
        
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (i, 0, n), (k, 0, m))
    
    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)


if __name__ == '__main__':
    prove(__file__)
