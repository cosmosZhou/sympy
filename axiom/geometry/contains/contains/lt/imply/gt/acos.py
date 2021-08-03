from util import *


@apply
def apply(contains, contains_y, lt):
    x, domain_x = contains.of(Contains)
    y, domain_y = contains_y.of(Contains)    
    assert domain_x in Interval(-1, 1)
    assert domain_y in Interval(-1, 1, right_open=True)
    return acos(x) > acos(y)


@prove
def prove(Eq):
    from axiom import algebra, geometry, sets

    x, y = Symbol(real=True)
    Eq << apply(Contains(x, Interval(-1, 1)), Contains(y, Interval(-1, 1, right_open=True)), x < y)

    Eq << algebra.gt.given.is_positive.apply(Eq[3])

    Eq << geometry.sin.to.add.principle.sub.apply(sin(Eq[-1].lhs))

    Eq << sets.lt.contains.contains.imply.gt.sqrt.apply(Eq[2], Eq[0], Eq[1])

    Eq << algebra.gt.imply.is_positive.apply(Eq[-1])

    Eq << algebra.eq.gt.imply.gt.add.apply(Eq[-3], Eq[-1])

    Eq << Contains(acos(x), Interval(0, S.Pi), plausible=True)


if __name__ == '__main__':
    run()