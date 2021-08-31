from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(0, 1, left_open=True, right_open=True)
    assert domain_y in Interval(0, 1, left_open=True, right_open=True)
    _x, _y = lt.of(Less)
    assert _x == x
    assert _y == y
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(0, 1, left_open=True, right_open=True)), Element(y, Interval(0, 1, left_open=True, right_open=True)))

    Eq << Greater(y ** 2 * (1 - x ** 2), x ** 2 * (1 - y ** 2), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << algebra.lt.imply.is_positive.apply(Eq[0])

    Eq.x_is_positive = sets.el.imply.is_positive.apply(Eq[1])

    Eq.y_is_positive = sets.el.imply.is_positive.apply(Eq[2])

    Eq << Eq.y_is_positive + Eq.x_is_positive

    Eq << Eq[-1] * Eq[-2]

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.is_positive.imply.gt.apply(Eq[-1])

    Eq << sets.el.imply.sqrt_is_positive.apply(Eq[2])

    Eq << algebra.is_positive.imply.is_positive.square.apply(Eq[-1])

    Eq << algebra.is_positive.imply.is_positive.square.apply(Eq.x_is_positive)

    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[-2])

    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[-1])

    Eq << algebra.is_nonnegative.gt.imply.gt.sqrt.apply(Eq[-1], Eq[4])

    Eq <<= algebra.is_positive.imply.eq.abs.apply(Eq.x_is_positive), algebra.is_positive.imply.eq.abs.apply(Eq.y_is_positive)
    Eq << Eq[-3].subs(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()