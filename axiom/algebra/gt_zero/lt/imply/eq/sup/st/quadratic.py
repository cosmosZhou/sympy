from util import *


@apply
def apply(is_positive, lt, fx, x=None, left_open=True, right_open=True):
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = is_positive.of(Expr > 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(y0, y1))


@prove
def prove(Eq):
    from axiom import algebra

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a > 0, m < M, a * x ** 2 + b * x + c, x)

    Eq.a_reciprocal = algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.sup.limits.subs.offset, -b * Eq.a_reciprocal.lhs / 2)

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.add)
    Eq.eq = Eq[-1].this.lhs.expr.expand()

    Eq << Eq[1] + Eq.a_reciprocal.lhs * b / 2

    Eq << algebra.lt.imply.eq.sup_square.to.max.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.eq.mul.to.sup.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq.eq.subs(Eq[-1].reversed)

    Eq << algebra.gt_zero.imply.eq.mul.to.max.apply(Eq[0], Eq[-1].lhs.find(Max))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.max)

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()
# created on 2019-09-09
