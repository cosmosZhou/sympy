from util import *


@apply
def apply(contains1, contains2):
    x, sx = contains1.of(Contains)
    y, sy = contains2.of(Contains)

    a, b = sx.of(Interval)
    _b, c = sy.of(Interval)
    assert b <= _b

    return LessEqual(x, y)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    c = Symbol.c(integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Contains(x, Interval(a, b, left_open=True)), Contains(y, Interval(b, c)))

    Eq << sets.contains.imply.conds.split.interval.apply(Eq[0])

    Eq << sets.contains.imply.conds.split.interval.apply(Eq[1])

    Eq << algebra.le.ge.imply.le.transit.apply(Eq[-3], Eq[-2])

    

    

    

    


if __name__ == '__main__':
    run()