from axiom.utility import prove, apply

from sympy import *
from axiom import algebre, sets

from tensorflow.nn.convolutional.same import conv2d


@apply
def apply(x, w, r, *indices):
    (β0, ζ0), (β1, ζ1) = indices
    
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    t = Symbol.t(integer=True)
    
    m, n0, n1, d = x.shape
    l0, l1, _d, d_ = w.shape
    assert d == _d
    
    M = Symbol.M(LAMBDA[j:n1, i:n0, k:m](Boole((i >= β0[k]) & (i < ζ0[k]) & (j >= β1[k]) & (j < ζ1[k]))))
    
    M0 = LAMBDA[t:d, j:n1, i:n0, k:m](M[k, i, j])
    M1 = LAMBDA[t:d_, j:n1, i:n0, k:m](M[k, i, j])
    
    block = conv2d[r](x[k][β0[k]:ζ0[k], β1[k]:ζ1[k]], w)
#     print(block.shape)
    
    block = BlockMatrix[1](ZeroMatrix(ζ0[k] - β0[k], β1[k], d_), block, ZeroMatrix(ζ0[k] - β0[k], n1 - ζ1[k], d_))
#     print(block.shape)
    
    block = BlockMatrix(ZeroMatrix(β0[k], n1, d_), block, ZeroMatrix(n0 - ζ0[k], n1, d_))
#     print(block.shape)
    
    return Equality(conv2d[r](x * M0, w) * M1, LAMBDA[k:m](block))


@prove
def prove(Eq):
    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(shape=(2,), integer=True, positive=True)    
    
    d = Symbol.d(integer=True, positive=True)
    d_ = Symbol("d'", integer=True, positive=True)
    
    l = Symbol.l(shape=(2,), integer=True, positive=True)
    
    # r = dilation rate
    r = Symbol.r(shape=(2,), integer=True, positive=True)

    β0 = Symbol("β^0", shape=(m,), domain=Interval(0, n[0] - 1, integer=True))
    ζ0 = Symbol("ζ^0", shape=(m,), domain=Interval(1, n[0], integer=True))
    
    β1 = Symbol("β^1", shape=(m,), domain=Interval(0, n[1] - 1, integer=True))
    ζ1 = Symbol("ζ^1", shape=(m,), domain=Interval(1, n[1], integer=True))
    
    x = Symbol.x(real=True, shape=(m, n[0], n[1], d))
    w = Symbol.w(real=True, shape=(l[0], l[1], d, d_))
    
    Eq << apply(x, w, r, (β0, ζ0), (β1, ζ1))
    
    Eq << Eq[-1].rhs.function.args[1].args[1].this.definition
    
    d0 = Symbol.d0((l[0] - 1) // 2 * r[0] + (r[0] // 2) * (1 - l[0] % 2))
    d1 = Symbol.d1((l[1] - 1) // 2 * r[1] + (r[1] // 2) * (1 - l[1] % 2))
    
    Eq.conv2d = Eq[-1].subs(d0.this.definition.reversed).subs(d1.this.definition.reversed)
    
    C = Symbol.C(Eq[1].lhs)

    Eq << C.this.definition
    
    Eq << Eq[-1].this.rhs.args[0].definition
        
    Eq << Eq[-1].subs(d0.this.definition.reversed).subs(d1.this.definition.reversed)
    
    k, i, j = Eq[0].lhs.indices
    
    Eq << Eq[-1][k, i, j]

    Eq << Eq[-1].this.rhs.args[1].function.args[0].args[1].function.definition
    
    Eq << Eq[-1].this.rhs.args[1].function.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].function.apply(algebre.piecewise.ripple, var=i)
    
    Eq << Eq[-1].this.rhs.args[1].apply(algebre.sum.limits.split.piecewise)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][2].args[1].args[1].args[1].apply(algebre.ceiling.astype.plus.quotient)
    
    Eq << Eq[-1].this.rhs.args[1].limits[1][2].args[1].args[1].args[1].apply(algebre.ceiling.astype.plus.quotient)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][2].args[1].apply(algebre.min.astype.floor)
    
    Eq << Eq[-1].this.rhs.args[1].limits[1][2].args[1].apply(algebre.min.astype.floor)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].args[0].apply(algebre.times.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[1].limits[1][1].args[0].apply(algebre.times.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].args[2].arg.apply(algebre.times.distribute)    
    
    Eq << Eq[-1].this.rhs.args[1].limits[1][1].args[2].arg.apply(algebre.times.distribute)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].apply(algebre.max.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[1].limits[1][1].apply(algebre.max.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[1].limits[0][1].apply(algebre.ceiling.astype.max)
    
    Eq << Eq[-1].this.rhs.args[1].limits[1][1].apply(algebre.ceiling.astype.max)
    
    Eq << Eq[-1].this.rhs.args[0].definition
    
    Eq << Eq[-1].this.rhs.args[0].astype(Piecewise)
    
    Eq.convolution_definition = Eq[-1].this.rhs.astype(Piecewise)
    
    C_quote = Symbol("C'", Eq[1].rhs)
    
    Eq << C_quote.this.definition
    
    Eq << Eq[-1][k]
    
    Eq << Eq[-1].this.rhs.subs(Eq.conv2d)
    
    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.swap.front)
    
    Eq << Eq[-1][j]
    
    Eq << Eq[-1].this.rhs.args[0].expr.apply(algebre.piecewise.swap.front)
    
    Eq << Eq[-1].this.rhs.apply(algebre.piecewise.flatten, index=0)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][1].args[0].apply(algebre.times.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[1][1].args[0].apply(algebre.times.astype.ceiling)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][1].args[1].arg.apply(algebre.times.distribute)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[1][1].args[1].arg.apply(algebre.times.distribute)        
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[0][2].args[1].apply(algebre.min.astype.floor)
    
    Eq << Eq[-1].this.rhs.args[0].expr.limits[1][2].args[1].apply(algebre.min.astype.floor)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq.convolution_definition, Eq[-1])
        
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (j, 0, n[1]), (i, 0, n[0]), (k, 0, m))
    
    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)


if __name__ == '__main__':
    prove(__file__)
