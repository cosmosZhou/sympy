from util import *


@apply
def apply(ge, contains_y):
    if ge.is_Contains:
        ge, contains_y = contains_y, ge
    y, a = ge.of(GreaterEqual)
    _y, domain = contains_y.of(Contains)    
    assert y == _y
    b, c = domain.of(Interval)
    a = Max(b, a)
    return Contains(y, Interval(a, c, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c, x, y = Symbol(real=True)
    Eq << apply(x >= a, Contains(x, Interval(b, c)))

    Eq << sets.contains.given.et.split.interval.apply(Eq[2])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])

    Eq << algebra.ge.ge.imply.ge.max.rhs.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()