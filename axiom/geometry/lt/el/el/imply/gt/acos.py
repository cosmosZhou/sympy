from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    _x, _y = lt.of(Less)
    assert _x == x and _y == y
    return acos(x) > acos(y)


@prove
def prove(Eq):
    from axiom import algebra, geometry, sets

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1)), Element(y, Interval(-1, 1, right_open=True)))

    Eq << algebra.gt.given.is_positive.apply(Eq[3])

    Eq << geometry.sin.to.add.principle.sub.apply(sin(Eq[-1].lhs))

    Eq << sets.lt.el.el.imply.gt.sqrt.apply(Eq[0], Eq[1], Eq[2])

    Eq << algebra.gt.imply.is_positive.apply(Eq[-1])

    Eq.sin_is_positive = algebra.eq.gt.imply.gt.add.apply(Eq[-3], Eq[-1])

    Eq << geometry.imply.el.acos.apply(x)

    Eq << geometry.imply.el.acos.apply(y)

    Eq << sets.el.el.imply.el.sub.interval.apply(Eq[-2], Eq[-1])

    Eq << sets.el.imply.ou.split.interval.apply(Eq[-1], 0, left_open=True)

    Eq << Eq[-1].this.args[1].apply(geometry.el.imply.sin_is_nonpositive)

    Eq << algebra.cond.ou.imply.cond.apply(Eq.sin_is_positive, Eq[-1])

    Eq << sets.el.imply.is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()