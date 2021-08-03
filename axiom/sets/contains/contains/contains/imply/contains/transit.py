from util import *


@apply
def apply(contains_x, contains_y, contains_z):
    x, interval_x = contains_x.of(Contains)
    a, b = interval_x.of(Interval)
    left_open = interval_x.left_open
    
    y, interval_y = contains_y.of(Contains)
    c, d = interval_y.of(Interval)
    right_open = interval_y.right_open

    z, interval_z = contains_z.of(Contains)
    _x, _y = interval_z.of(Interval)
    assert _x == x and _y == y

    return Contains(z, Interval(a, d, left_open=left_open, right_open=right_open))

@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, d = Symbol(real=True)
    x, y, z = Symbol(real=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)), Contains(y, Interval(c, d, right_open=True)), Contains(z, Interval(x, y, left_open=True)))

    Eq << sets.contains.given.et.split.interval.apply(Eq[-1])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[2])

    Eq <<= sets.contains.imply.gt.split.interval.apply(Eq[0]), sets.contains.imply.lt.split.interval.apply(Eq[1])

    Eq << algebra.gt.gt.imply.gt.transit.apply(Eq[-4], Eq[-2])

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-3], Eq[-1])


if __name__ == '__main__':
    run()