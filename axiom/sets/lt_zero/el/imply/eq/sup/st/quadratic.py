from util import *


@apply
def apply(is_negative, el, fx, x=None):
    ab, interval = el.of(Element)
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    a = is_negative.of(Expr < 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    assert -ab * (2 * a) == b
    return Equal(Sup[x:interval](fx), c - b ** 2 / (4 * a))


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, Element(-b / (2 * a), Interval(m, M, left_open=True)), a * x ** 2 + b * x + c, x)

    Eq << Eq[-1].this.lhs.apply(algebra.sup.to.add)

    Eq << algebra.lt_zero.imply.eq.sup.to.mul.inf.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].this.find(Inf).expr.expand()

    Eq.is_positive = -Eq[0]

    Eq << algebra.gt_zero.imply.eq.inf.to.mul.apply(Eq.is_positive, Eq[-1].find(Inf))

    Eq << -Eq[-1].this.lhs.expr.expand()

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << sets.gt_zero.el.imply.eq.inf.st.quadratic.apply(Eq.is_positive, Eq[1], Eq[-1].find(Inf).expr, x)
    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-26
