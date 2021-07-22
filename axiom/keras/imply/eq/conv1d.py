from util import *


@apply
def apply(x, w, β, ζ, r):
    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m, n, d = x.shape
    l, _d, d_ = w.shape
    assert d == _d

    M = Symbol.M(Lamda[i:n, k:m](Bool((i >= β[k]) & (i < ζ[k]))))

    M0 = Lamda[j:d, i:n, k:m](M[k, i])
    M1 = Lamda[j:d_, i:n, k:m](M[k, i])

    return Equal(conv1d[r](x * M0, w) * M1, Lamda[k:m](BlockMatrix(ZeroMatrix(β[k], d_),
                                                                   conv1d[r](x[k][β[k]:ζ[k]], w),
                                                                   ZeroMatrix(n - ζ[k], d_))))


@prove
def prove(Eq):
    from axiom import algebra

    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    d = Symbol.d(integer=True, positive=True)
    d_ = Symbol("d'", integer=True, positive=True)
    l = Symbol.l(integer=True, positive=True)
    #r = dilation rate
    r = Symbol.r(integer=True, positive=True)
    β = Symbol.β(shape=(m,), domain=Range(0, n))
    ζ = Symbol.ζ(shape=(m,), domain=Range(1, n + 1))
    x = Symbol.x(real=True, shape=(m, n, d))
    w = Symbol.w(real=True, shape=(l, d, d_))
    Eq << apply(x, w, β, ζ, r)

    Eq << Eq[-1].rhs.expr.args[1].this.defun()

    d0 = Symbol.d0((l - 1) // 2 * r + (r // 2) * (1 - l % 2))
    Eq.conv1d = Eq[-1].subs(d0.this.definition.reversed, evaluate=False)

    C = Symbol.C(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.rhs.args[0].defun()

    Eq << Eq[-1].subs(d0.this.definition.reversed)

    k, i = Eq[0].lhs.indices
    Eq << Eq[-1][k, i]

    Eq << Eq[-1].this.find(Sum, Lamda).expr.definition

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.find(Min, Add).apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min).apply(algebra.min.to.add, 1)

    Eq << Eq[-1].this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Max[Ceiling]).apply(algebra.max.to.ceiling)

    Eq << Eq[-1].this.find(Ceiling[Max]).apply(algebra.ceiling.to.max)

    Eq << Eq[-1].this.find(~Indexed * Sum).definition

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(algebra.mul_piecewise.to.piecewise)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv1d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.swap.front)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.convolution_definition, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)


if __name__ == '__main__':
    run()
