from util import *


@apply
def apply(eq_M, x, w, r):
    ((i, (β, ζ)), (S[i], S[0], n), (k, S[0], m)), M = eq_M.of(Equal[Lamda[Bool[Element[Range]]]])

    β, S[k] = β.of(Indexed)
    ζ, S[k] = ζ.of(Indexed)

    S[m], S[n], d = x.shape
    l, S[d], d_ = w.shape

    j = Symbol(integer=True)
    M0 = Lamda[j:d, i:n, k:m](M[k, i])
    M1 = Lamda[j:d_, i:n, k:m](M[k, i])

    return Equal(conv1d[r](x * M0, w) * M1, Lamda[k:m](BlockMatrix(ZeroMatrix(β[k], d_),
                                                                   conv1d[r](x[k][β[k]:ζ[k]], w),
                                                                   ZeroMatrix(n - ζ[k], d_))))


@prove
def prove(Eq):
    from axiom import sets, algebra

    m, n, d, d_quote, l, r = Symbol(integer=True, positive=True)
    #r is the dilation rate
    β = Symbol(shape=(m,), domain=Range(n))
    ζ = Symbol(shape=(m,), domain=Range(1, n + 1))
    x = Symbol(real=True, shape=(m, n, d))
    w = Symbol(real=True, shape=(l, d, d_quote))
    M = Symbol(real=True, shape=(m, n))
    i, k = Symbol(integer=True)
    Eq << apply(Equal(M, Lamda[i:n, k:m](Bool(Element(i, Range(β[k], ζ[k]))))),
                x, w, r)

    Eq.M_def = Eq[0].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].rhs.expr.args[1].this.defun()

    d0 = Symbol((l - 1) // 2 * r + (r // 2) * (1 - l % 2))
    Eq.conv1d = Eq[-1].subs(d0.this.definition.reversed, evaluate=False)

    C = Symbol(Eq[1].lhs)
    Eq << C.this.definition

    Eq << Eq[-1].this.rhs.args[0].defun()

    Eq << Eq[-1].subs(d0.this.definition.reversed)

    Eq << Eq[-1][k, i]

    Eq << Eq[-1].this.find(Sum, Lamda).subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.find(Min, Add).apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(Min).apply(algebra.min.to.add, 1)

    Eq << Eq[-1].this.find(Add[Ceiling]).apply(algebra.add_ceiling.to.floor)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.rhs.subs(Eq.M_def)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq.convolution_definition = Eq[-1].this.rhs.apply(algebra.mul.to.piece)

    C_quote = Symbol("C'", Eq[1].rhs)
    Eq << C_quote.this.definition

    Eq << Eq[-1][k]

    Eq << Eq[-1].this.rhs.subs(Eq.conv1d)

    Eq << Eq[-1][i]

    Eq << Eq[-1].this.rhs.apply(algebra.piece.swap)

    Eq << Eq[-1].this.find(-Floor).apply(algebra.mul.to.ceiling)

    Eq << Eq[-1].this.find(-Add).apply(algebra.mul.distribute)

    Eq << Eq[-1].this.find(Min[Floor]).apply(algebra.min.to.floor)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.convolution_definition, Eq[-1])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (i, 0, n), (k, 0, m))

    Eq << Eq[-1].subs(C.this.definition, C_quote.this.definition)





if __name__ == '__main__':
    run()
# created on 2021-01-01
# updated on 2022-01-23
