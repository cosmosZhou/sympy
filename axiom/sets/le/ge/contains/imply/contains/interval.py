from util import *


@apply
def apply(le, ge, contains):
    _a, a = le.of(LessEqual)
    _b, b = ge.of(GreaterEqual)
    x, domain = contains.of(Contains)
    a_, b_ = domain.of(Interval)
    assert a == a_ and b == b_
    
    return Contains(x, Interval(_a, _b, left_open=domain.left_open, right_open=domain.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, a_quote, b_quote, x = Symbol(real=True, given=True)
    Eq << apply(a_quote <= a, b_quote >= b, Contains(x, Interval(a, b, right_open=True)))

    Eq << sets.contains.given.et.split.interval.apply(Eq[-1])

    Eq << sets.contains.imply.et.split.interval.apply(Eq[2])

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[-2], Eq[0])
    Eq << algebra.lt.ge.imply.lt.transit.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()