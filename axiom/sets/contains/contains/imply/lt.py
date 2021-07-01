from util import *


@apply
def apply(contains1, contains2):
    x, sx = contains1.of(Contains)
    y, sy = contains2.of(Contains)

    a, b = sx.of(Interval)
    _b, c = sy.of(Interval)
    if not sx.right_open and not sy.left_open:
        assert b < _b
    else:
        assert b <= _b

    return Less(x, y)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    c = Symbol.c(integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)), Contains(y, Interval(b, c, left_open=True)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])

    Eq << algebra.le.gt.imply.lt.transit.apply(Eq[-3], Eq[-2])


if __name__ == '__main__':
    run()