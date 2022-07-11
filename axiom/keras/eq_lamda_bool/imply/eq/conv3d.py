from util import *


@apply
def apply(eq_M, x, w, r):
    (((i, (β0, ζ0)), (j, (β1, ζ1)), (t, (β2, ζ2))), (S[t], S[0], n2), (S[j], S[0], n1), (S[i], S[0], n0), (k, S[0], m)), M = eq_M.of(Equal[Lamda[Bool[Element[Range] & Element[Range] & Element[Range]]]])

    β0, S[k] = β0.of(Indexed)
    ζ0, S[k] = ζ0.of(Indexed)

    β1, S[k] = β1.of(Indexed)
    ζ1, S[k] = ζ1.of(Indexed)

    β2, S[k] = β2.of(Indexed)
    ζ2, S[k] = ζ2.of(Indexed)

    S[m], S[n0], S[n1], S[n2], d = x.shape
    l0, l1, l2, S[d], d_ = w.shape

    h = Symbol(integer=True)
    M0 = Lamda[h:d, t:n2, j:n1, i:n0, k:m](M[k, i, j, t])
    M1 = Lamda[h:d_, t:n2, j:n1, i:n0, k:m](M[k, i, j, t])

    block = conv3d[r](x[k][β0[k]:ζ0[k], β1[k]:ζ1[k], β2[k]:ζ2[k]], w)

    block = BlockMatrix[2](ZeroMatrix(ζ0[k] - β0[k], ζ1[k] - β1[k], β2[k], d_), block, ZeroMatrix(ζ0[k] - β0[k], ζ1[k] - β1[k], n2 - ζ2[k], d_))

    block = BlockMatrix[1](ZeroMatrix(ζ0[k] - β0[k], β1[k], n2, d_), block, ZeroMatrix(ζ0[k] - β0[k], n1 - ζ1[k], n2, d_))

    block = BlockMatrix(ZeroMatrix(β0[k], n1, n2, d_), block, ZeroMatrix(n0 - ζ0[k], n1, n2, d_))

    return Equal(conv3d[r](x * M0, w) * M1, Lamda[k:m](block))


@prove(slow=True)
def prove(Eq):
    from axiom import sets, algebra

    m, d, d_quote = Symbol(integer=True, positive=True)
    n, l, r = Symbol(shape=(3,), integer=True, positive=True)
    #r is the dilation rate
    β0 = Symbol("β^0", shape=(m,), domain=Range(n[0]))
    ζ0 = Symbol("ζ^0", shape=(m,), domain=Range(1, n[0] + 1))
    β1 = Symbol("β^1", shape=(m,), domain=Range(n[1]))
    ζ1 = Symbol("ζ^1", shape=(m,), domain=Range(1, n[1] + 1))
    β2 = Symbol("β^2", shape=(m,), domain=Range(n[2]))
    ζ2 = Symbol("ζ^2", shape=(m,), domain=Range(1, n[2] + 1))
    x = Symbol(real=True, shape=(m, n[0], n[1], n[2], d))
    w = Symbol(real=True, shape=(l[0], l[1], l[2], d, d_quote))
    M = Symbol(real=True, shape=(m, n[0], n[1], n[2]))
    i, j, t, k = Symbol(integer=True)
    Eq << apply(Equal(M, Lamda[t:n[2], j:n[1], i:n[0], k:m](Bool(Element(i, Range(β0[k], ζ0[k])) & Element(j, Range(β1[k], ζ1[k])) & Element(t, Range(β2[k], ζ2[k]))))),
                x, w, r)

    Eq.M_def = Eq[0].this.find(Element).apply(sets.el_range.to.et).this.find(Element).apply(sets.el_range.to.et).this.find(Element).apply(sets.el_range.to.et)
    Eq << Eq[1].rhs.find(conv3d).this.defun()

    d0 = Symbol((l[0] - 1) // 2 * r[0] + (r[0] // 2) * (1 - l[0] % 2))
    d1 = Symbol((l[1] - 1) // 2 * r[1] + (r[1] // 2) * (1 - l[1] % 2))
    d2 = Symbol((l[2] - 1) // 2 * r[2] + (r[2] // 2) * (1 - l[2] % 2))
    Eq.conv3d = Eq[-1].subs(d0.this.definition.reversed, simplify=False).subs(d1.this.definition.reversed, simplify=False).subs(d2.this.definition.reversed, simplify=False)

    C = Symbol(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.rhs.args[0].defun()

    Eq << Eq[-1].subs(d0.this.definition.reversed, simplify=False).subs(d1.this.definition.reversed, simplify=False).subs(d2.this.definition.reversed, simplify=False)

    Eq << Eq[-1][k, i, j, t]

    Eq << Eq[-1].this.find(Sum, Lamda).subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.ripple, var=i)

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piece.ripple, var=j)







    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.split.piece).this.find(Sum).apply(algebra.sum.limits.split.piece)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.split.by_parts)

    Eq << Eq[-1].this.find(Min, Add[Min]).apply(algebra.add.to.min).this.find(Min, Add[Min]).apply(algebra.add.to.min).this.find(Min, Add[Min]).apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min[Ceiling]).apply(algebra.min.to.add, 1).this.find(Min[Ceiling]).apply(algebra.min.to.add, 1).this.find(Min[Ceiling]).apply(algebra.min.to.add, 1)

    Eq << Eq[-1].this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor).this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor).this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.rhs.subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv3d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)

    Eq << Eq[-1][j]

    Eq << Eq[-1].this.find(Piecewise, Piecewise).apply(algebra.piece.swap)

    Eq << Eq[-1][t]

    Eq << Eq[-1].this.find(Piecewise, Piecewise, Piecewise).apply(algebra.piece.swap)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.flatten)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling).this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute).this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor).this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.convolution_definition, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (t, 0, n[2]), (j, 0, n[1]), (i, 0, n[0]), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)





if __name__ == '__main__':
    run()
# created on 2021-01-02
# updated on 2022-01-23
