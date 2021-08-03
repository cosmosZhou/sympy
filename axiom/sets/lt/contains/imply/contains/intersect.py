from util import *


@apply
def apply(lt, contains_y):
    y, _b = lt.of(Less)
    _y, domain = contains_y.of(Contains)    
    assert y == _y
    a, b = domain.of(Interval)
    b = Min(b, _b)
    return Contains(y, Interval(a, b, left_open=domain.left_open, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, y = Symbol(real=True)
    Eq << apply(x < b, Contains(x, Interval(a, b)))

    Eq << sets.contains.given.et.split.interval.apply(Eq[2])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])


if __name__ == '__main__':
    run()