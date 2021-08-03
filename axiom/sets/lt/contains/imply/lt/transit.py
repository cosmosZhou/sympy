from util import *


@apply
def apply(lt, contains_y):
    y, domain_y = contains_y.of(Contains)    
    a, b = domain_y.of(Interval)
    x, _y = lt.of(Less)
    assert _y == y
    return x < b


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(x < y, Contains(y, Interval(a, b)))

    Eq << sets.contains.imply.le.split.interval.apply(Eq[1])

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()