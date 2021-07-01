from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
    m, M = interval.of(Interval, None)
    assert not interval.left_open
    assert not interval.right_open
    assert M.is_zero
    return LessEqual(x * x, m * m)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    Eq << apply(Contains(x, Interval(m, 0)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq << algebra.is_nonpositive.ge.imply.le.square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

