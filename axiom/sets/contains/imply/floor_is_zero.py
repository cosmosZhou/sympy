from util import *


@apply
def apply(contains):
    x, domain = contains.of(Contains)
    assert domain in Interval(0, 1, right_open=True)
    return Equal(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True)
    Eq << apply(Contains(x, Interval(0, 1, right_open=True)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])
    Eq << algebra.is_nonnegative.lt.imply.floor_is_zero.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()