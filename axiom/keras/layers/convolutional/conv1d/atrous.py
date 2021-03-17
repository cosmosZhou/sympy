from axiom.utility import prove, apply

from sympy import *
from axiom import algebre, sets

from tensorflow.nn.convolutional.same import conv1d


@apply
def apply(x, w, β, ζ, r): 
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m, n, d = x.shape
    l, _d, d_ = w.shape
    assert d == _d
    
    M = Symbol.M(LAMBDA[i:n, k:m](Boole((i >= β[k]) & (i < ζ[k]))))
    
    M0 = LAMBDA[j:d, i:n, k:m](M[k, i])
    M1 = LAMBDA[j:d_, i:n, k:m](M[k, i])
    
    return Equality(conv1d[r](x * M0, w) * M1,
                    LAMBDA[k:m](BlockMatrix(ZeroMatrix(β[k], d_),
                                            conv1d[r](x[k][β[k]:ζ[k]], w),
                                            ZeroMatrix(n - ζ[k], d_))))


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    d = Symbol.d(integer=True, positive=True)
    d_ = Symbol("d'", integer=True, positive=True)
    l = Symbol.l(integer=True, positive=True)
    # r = dilation rate
    r = Symbol.r(integer=True, positive=True)

    β = Symbol.β(shape=(m,), domain=Interval(0, n - 1, integer=True))
    ζ = Symbol.ζ(shape=(m,), domain=Interval(1, n, integer=True))
    x = Symbol.x(real=True, shape=(m, n, d))
    w = Symbol.w(real=True, shape=(l, d, d_))
    
    Eq << apply(x, w, β, ζ, r)
    
    Eq << Eq[-1].rhs.function.args[1].this.definition
    
    d0 = Symbol.d0((l - 1) // 2 * r + (r // 2) * (1 - l % 2))
    
    Eq.conv1d = Eq[-1].subs(d0.this.definition.reversed)
    
    C = Symbol.C(Eq[1].lhs)

    Eq << C.this.definition
    
    Eq << Eq[-1].this.rhs.args[0].definition
        
    Eq << Eq[-1].subs(d0.this.definition.reversed)
    
    k, i = Eq[0].lhs.indices
    
    Eq << Eq[-1][k, i]

    Eq << Eq[-1].this.rhs.args[1].function.args[0].args[1].function.definition
    
    Eq << Eq[-1].this.rhs.args[1].function.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][2].args[1].args[1].args[1].apply(algebre.ceiling.astype.plus.quotient)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][2].args[1].apply(algebre.min.astype.floor)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].args[0].apply(algebre.times.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].args[2].arg.apply(algebre.times.distribute)
            
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].apply(algebre.max.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].apply(algebre.ceiling.astype.max)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[0].astype(Piecewise)
    
    Eq.convolution_definition = Eq[-1].this.rhs.astype(Piecewise)
    
    C_quote = Symbol("C'", Eq[1].rhs)
    
    Eq << C_quote.this.definition
    
    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv1d)
    
    Eq << Eq[-1][i]
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.swap.front)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][1].args[0].apply(algebre.times.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][1].args[1].arg.apply(algebre.times.distribute)
        
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][2].args[1].apply(algebre.min.astype.floor)
    
    Eq << algebre.eq.eq.imply.eq.transit.apply(Eq.convolution_definition, Eq[-1])
        
    Eq << algebre.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n), (k, 0, m))
    
    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)


if __name__ == '__main__':
    prove(__file__)
