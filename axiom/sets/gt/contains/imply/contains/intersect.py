from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    _y, domain = contains_y.of(Contains)    
    assert y == _y
    a, b = domain.of(Interval)
    a = Max(a, _a)    
    return Contains(y, Interval(a, b, left_open=True, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x, y = Symbol(real=True)
    Eq << apply(x > a, Contains(x, Interval(a, b)))

    Eq << sets.contains.given.et.split.interval.apply(Eq[2])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[1])


if __name__ == '__main__':
    run()