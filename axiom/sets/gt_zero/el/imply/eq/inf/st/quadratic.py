from util import *


@apply
def apply(is_positive, el, fx, x=None):
    ab, interval = el.of(Element)
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    a = is_positive.of(Expr > 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    assert -ab * (2 * a) == b
    return Equal(Inf[x:interval](fx), c - b ** 2 / (4 * a))


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(a > 0, Element(-b / (2 * a), Interval(m, M, right_open=True)), a * x ** 2 + b * x + c, x)

    Eq << Eq[-1].this.lhs.apply(algebra.inf.limits.subs.offset, Eq[1].lhs)

    Eq << Eq[-1].this.lhs.expr.expand()

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << algebra.gt_zero.imply.eq.inf.to.mul.apply(Eq[-1], Eq[-2].lhs) * a

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << algebra.eq.given.eq.div.apply(Eq[-1], a)

    Eq << sets.el.imply.el.sub.apply(Eq[1], Eq[1].lhs)

    Eq << sets.el_interval.imply.et.apply(Eq[-1])

    Eq << algebra.gt_zero.le_zero.imply.eq.inf_square.to.zero.apply(Eq[-1], Eq[-2], left_open=False, x=x)


if __name__ == '__main__':
    run()
# created on 2019-12-25
