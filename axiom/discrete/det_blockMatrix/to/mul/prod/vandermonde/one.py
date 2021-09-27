from util import *


@apply
def apply(r, n):
    assert n >= 2
    k, i = Symbol(integer=True)
    j = Symbol(domain=Range(0, n))

    A = Lamda[j, i:n - 1]((j + 1) ** (i + 1))
    R = Lamda[j](1 - r ** (j + 1))

    return Equal(Det([R, A]), (1 - r) ** n * Product[k:1:n](factorial(k)))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    r = Symbol(real=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(r, n)

    (j, *_), (i, *iab) = Eq[0].lhs.arg.args[1].limits
    E = Lamda[j, i:n]((-1) ** (j - i) * binomial(j + 1, i + 1))
    Eq << (Eq[0].lhs.arg @ E).this.apply(discrete.matmul.to.blockMatrix)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.lamda)

    (k, *_), *_ = Eq[-1].rhs.args[1].expr.limits
    _i = i.copy(domain=Range(*iab))
    Eq << discrete.stirling2.to.mul_sum.apply(_i + 1, j + 1)

    Eq << Eq[-1] * factorial(j + 1)

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.lhs.simplify()

    Eq << algebra.cond.imply.all.apply(Eq[-1], _i)

    Eq << Eq[3].rhs.args[1].expr.this.apply(algebra.sum.limits.subs.offset, -1)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-2], Eq[-1])

    Eq.equation = algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[3])

    Eq << Eq.equation.rhs.args[0].expr.this.apply(algebra.sum.limits.subs.offset, -1)

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << discrete.pow.to.sum.binomial.theorem.apply(r, -1, j + 1, i)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.args[1].simplify()

    Eq << Eq[-4] + (Eq[-1] - Eq[-1].lhs)

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq[-1].this.rhs.args[-1].args[-1].expr.powsimp()

    Eq << discrete.pow.to.sum.binomial.theorem.apply(1, -1, j + 1, i)

    Eq << (-Eq[-1]).this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-3] + Eq[-1]

    Eq << Eq[-1].this.rhs.simplify()

    Eq << Eq.equation.subs(Eq[-1])

    Eq << discrete.eq.imply.eq.rmatmul.apply(Eq[-1], ShiftMatrix(n, 0, n - 1))

    Eq << Eq[-1].apply(discrete.eq.imply.eq.det)

    Eq << Eq[-1].this.lhs.apply(discrete.det.to.mul)

    Eq << Eq[-1] * (-1) ** (n - 1)

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.limits.subs.offset, -1)


if __name__ == '__main__':
    run()
