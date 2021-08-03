from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Contains)
    y, domain_y = contains_y.of(Contains)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    _x, _y = lt.of(Less)
    assert _x == x
    assert _y == y
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y, Contains(x, Interval(-1, 1)), Contains(y, Interval(-1, 1, right_open=True)))

    Eq << sets.lt.contains.imply.lt.transit.apply(Eq[0], Eq[2])

    Eq.x_contains = sets.lt.contains.imply.contains.intersect.apply(Eq[-1], Eq[1])

    Eq << sets.gt.contains.imply.gt.transit.apply(Eq[0].reversed, Eq[1])

    Eq.y_contains = sets.gt.contains.imply.contains.intersect.apply(Eq[-1], Eq[2])

    Eq << algebra.cond.given.et.suffice.split.apply(Eq[3], cond=Equal(x, -1))

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-2])

    Eq << algebra.suffice.given.cond.apply(Eq[-1])

    Eq << -sets.contains.imply.lt.square.apply(Eq.y_contains) + 1

    Eq << algebra.is_positive.imply.is_positive.sqrt.apply(Eq[-1])

    Eq << algebra.cond.imply.suffice.apply(Eq.x_contains, cond=Eq[-4].lhs)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.ne.contains.imply.contains)

    Eq << algebra.cond.suffice.imply.suffice.et.rhs.apply(Eq.y_contains & Eq[0], Eq[-1])


if __name__ == '__main__':
    run()