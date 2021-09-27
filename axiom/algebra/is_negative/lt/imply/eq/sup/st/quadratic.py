from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)

    x, _a, b, c = quadratic_coefficient(fx, x=x)
    assert _a == a

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    interval = Interval(m, M, left_open=left_open, right_open=right_open)
    return Equal(Sup[x:interval](fx),
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), interval)),
                           (Max(y0, y1), True)))


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x ** 2 + b * x + c, x)

    Eq << Eq[-1].this.lhs.apply(algebra.sup.to.add)

    Eq << Eq[-1].this.find(Max).apply(algebra.max.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.add)

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[-1], cond=Eq[-1].find(Element))

    Eq <<= algebra.suffice.given.suffice.subs.bool.apply(Eq[-2]), algebra.suffice.given.suffice.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= algebra.suffice.given.et.suffice_et.apply(Eq[-2], cond=Eq[0]), Eq[-1].this.lhs.apply(sets.notin.imply.ou.split.interval)

    Eq <<= Eq[-2].this.lhs.apply(sets.is_negative.el.imply.eq.sup.st.quadratic, Eq[-2].find(Sup).expr, x), algebra.suffice.given.et.suffice.split.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()