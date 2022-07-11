from util import *


@apply
def apply(eq_M, x, w, r):
    (((i, (β0, ζ0)), (j, (β1, ζ1))), (S[j], S[0], n1), (S[i], S[0], n0), (k, S[0], m)), M = eq_M.of(Equal[Lamda[Bool[Element[Range] & Element[Range]]]])

    β0, S[k] = β0.of(Indexed)
    ζ0, S[k] = ζ0.of(Indexed)

    β1, S[k] = β1.of(Indexed)
    ζ1, S[k] = ζ1.of(Indexed)


    S[m], S[n0], S[n1], d = x.shape
    l0, l1, S[d], d_ = w.shape

    t = Symbol(integer=True)
    M0 = Lamda[t:d, j:n1, i:n0, k:m](M[k, i, j])
    M1 = Lamda[t:d_, j:n1, i:n0, k:m](M[k, i, j])

    block = conv2d[r](x[k][β0[k]:ζ0[k], β1[k]:ζ1[k]], w)

    block = BlockMatrix[1](ZeroMatrix(ζ0[k] - β0[k], β1[k], d_), block, ZeroMatrix(ζ0[k] - β0[k], n1 - ζ1[k], d_))

    block = BlockMatrix(ZeroMatrix(β0[k], n1, d_), block, ZeroMatrix(n0 - ζ0[k], n1, d_))

    return Equal(conv2d[r](x * M0, w) * M1, Lamda[k:m](block))


@prove(slow=True)
def prove(Eq):
    from axiom import sets, algebra

    m, d, d_quote = Symbol(integer=True, positive=True)
    n, l, r = Symbol(shape=(2,), integer=True, positive=True)
    #r = dilation rate
    β0 = Symbol("β^0", shape=(m,), domain=Range(n[0]))
    ζ0 = Symbol("ζ^0", shape=(m,), domain=Range(1, n[0] + 1))
    β1 = Symbol("β^1", shape=(m,), domain=Range(n[1]))
    ζ1 = Symbol("ζ^1", shape=(m,), domain=Range(1, n[1] + 1))
    x = Symbol(real=True, shape=(m, n[0], n[1], d))
    w = Symbol(real=True, shape=(l[0], l[1], d, d_quote))
    M = Symbol(real=True, shape=(m, n[0], n[1]))
    i, j, k = Symbol(integer=True)
    Eq << apply(Equal(M, Lamda[j:n[1], i:n[0], k:m](Bool(Element(i, Range(β0[k], ζ0[k])) & Element(j, Range(β1[k], ζ1[k]))))),
                x, w, r)

    Eq.M_def = Eq[0].this.find(Element).apply(sets.el_range.to.et).this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].rhs.find(conv2d).this.defun()

    d0 = Symbol((l[0] - 1) // 2 * r[0] + (r[0] // 2) * (1 - l[0] % 2))
    d1 = Symbol((l[1] - 1) // 2 * r[1] + (r[1] // 2) * (1 - l[1] % 2))
    Eq.conv2d = Eq[-1].subs(d0.this.definition.reversed).subs(d1.this.definition.reversed)

    C = Symbol(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.find(conv2d).defun()

    Eq << Eq[-1].subs(d0.this.definition.reversed).subs(d1.this.definition.reversed)

    Eq << Eq[-1][k, i, j]

    Eq << Eq[-1].this.find(Sum, Lamda).subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.ripple, var=i)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.split.piece)

    Eq << Eq[-1].this.find(Min, Add[Min]).apply(algebra.add.to.min).this.find(Min, Add[Min]).apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min[Ceiling]).apply(algebra.min.to.add, 1).this.find(Min[Ceiling]).apply(algebra.min.to.add, 1)

    Eq << Eq[-1].this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor).this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.rhs.subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv2d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)

    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piece.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.convolution_definition, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n[1]), (i, 0, n[0]), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)





if __name__ == '__main__':
    run()
# created on 2021-01-01
# updated on 2022-01-23
