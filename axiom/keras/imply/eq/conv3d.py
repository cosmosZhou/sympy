from util import *


@apply
def apply(x, w, r, *indices):
    (β0, ζ0), (β1, ζ1), (β2, ζ2) = indices

    k = Symbol.k(integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    t = Symbol.t(integer=True)
    h = Symbol.h(integer=True)

    m, n0, n1, n2, d = x.shape
    l0, l1, l2, _d, d_ = w.shape
    assert d == _d

    M = Symbol.M(Lamda[t:n2, j:n1, i:n0, k:m](Bool((i >= β0[k]) & (i < ζ0[k]) & (j >= β1[k]) & (j < ζ1[k]) & (t >= β2[k]) & (t < ζ2[k]))))

    M0 = Lamda[h:d, t:n2, j:n1, i:n0, k:m](M[k, i, j, t])
    M1 = Lamda[h:d_, t:n2, j:n1, i:n0, k:m](M[k, i, j, t])

    block = conv3d[r](x[k][β0[k]:ζ0[k], β1[k]:ζ1[k], β2[k]:ζ2[k]], w)

    block = BlockMatrix[2](ZeroMatrix(ζ0[k] - β0[k], ζ1[k] - β1[k], β2[k], d_), block, ZeroMatrix(ζ0[k] - β0[k], ζ1[k] - β1[k], n2 - ζ2[k], d_))

    block = BlockMatrix[1](ZeroMatrix(ζ0[k] - β0[k], β1[k], n2, d_), block, ZeroMatrix(ζ0[k] - β0[k], n1 - ζ1[k], n2, d_))

    block = BlockMatrix(ZeroMatrix(β0[k], n1, n2, d_), block, ZeroMatrix(n0 - ζ0[k], n1, n2, d_))

    return Equal(conv3d[r](x * M0, w) * M1, Lamda[k:m](block))


@prove(slow=True)
def prove(Eq):
    from axiom import algebra

    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(shape=(3,), integer=True, positive=True)
    d = Symbol.d(integer=True, positive=True)
    d_ = Symbol("d'", integer=True, positive=True)
    l = Symbol.l(shape=(3,), integer=True, positive=True)
    #r is the dilation rate
    r = Symbol.r(shape=(3,), integer=True, positive=True)
    β0 = Symbol("β^0", shape=(m,), domain=Range(0, n[0]))
    ζ0 = Symbol("ζ^0", shape=(m,), domain=Range(1, n[0] + 1))
    β1 = Symbol("β^1", shape=(m,), domain=Range(0, n[1]))
    ζ1 = Symbol("ζ^1", shape=(m,), domain=Range(1, n[1] + 1))
    β2 = Symbol("β^2", shape=(m,), domain=Range(0, n[2]))
    ζ2 = Symbol("ζ^2", shape=(m,), domain=Range(1, n[2] + 1))
    x = Symbol.x(real=True, shape=(m, n[0], n[1], n[2], d))
    w = Symbol.w(real=True, shape=(l[0], l[1], l[2], d, d_))
    Eq << apply(x, w, r, (β0, ζ0), (β1, ζ1), (β2, ζ2))

    Eq << Eq[-1].rhs.find(conv3d).this.defun()

    d0 = Symbol.d0((l[0] - 1) // 2 * r[0] + (r[0] // 2) * (1 - l[0] % 2))
    d1 = Symbol.d1((l[1] - 1) // 2 * r[1] + (r[1] // 2) * (1 - l[1] % 2))
    d2 = Symbol.d2((l[2] - 1) // 2 * r[2] + (r[2] // 2) * (1 - l[2] % 2))
    Eq.conv3d = Eq[-1].subs(d0.this.definition.reversed, simplify=False).subs(d1.this.definition.reversed, simplify=False).subs(d2.this.definition.reversed, simplify=False)

    C = Symbol.C(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.rhs.args[0].defun()

    Eq << Eq[-1].subs(d0.this.definition.reversed, simplify=False).subs(d1.this.definition.reversed, simplify=False).subs(d2.this.definition.reversed, simplify=False)

    k, i, j, t = Eq[0].lhs.indices
    Eq << Eq[-1][k, i, j, t]

    Eq << Eq[-1].this.find(Sum, Lamda).expr.definition

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piecewise.ripple, var=i)

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piecewise.ripple, var=j)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.split.piecewise).this.find(Sum).apply(algebra.sum.limits.split.piecewise)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.split.by_parts)

    Eq << Eq[-1].this.find(Min, Add[Min]).apply(algebra.add.to.min).this.find(Min, Add[Min]).apply(algebra.add.to.min).this.find(Min, Add[Min]).apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min[Ceiling]).apply(algebra.min.to.add, 1).this.find(Min[Ceiling]).apply(algebra.min.to.add, 1).this.find(Min[Ceiling]).apply(algebra.min.to.add, 1)

    Eq << Eq[-1].this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor).this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor).this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Max[Ceiling]).apply(algebra.max.to.ceiling).this.find(Max[Ceiling]).apply(algebra.max.to.ceiling).this.find(Max[Ceiling]).apply(algebra.max.to.ceiling)

    Eq << Eq[-1].this.find(Ceiling[Max]).apply(algebra.ceiling.to.max).this.find(Ceiling[Max]).apply(algebra.ceiling.to.max).this.find(Ceiling[Max]).apply(algebra.ceiling.to.max)

    Eq << Eq[-1].this.find(~Indexed * Sum).definition

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(algebra.mul_piecewise.to.piecewise)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv3d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.swap.front)

    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piecewise.swap.front)

    Eq << Eq[-1][t]

    Eq << Eq[-1].this.find(Piecewise, Piecewise, Piecewise).apply(algebra.piecewise.swap.front)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.flatten)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.convolution_definition, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (t, 0, n[2]), (j, 0, n[1]), (i, 0, n[0]), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)


if __name__ == '__main__':
    run()
