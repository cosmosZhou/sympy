from util import *


@apply
def apply(given):
    x, interval = given.of(Contains)
    m, M = interval.of(Interval, None)
    assert not interval.left_open
    assert not interval.right_open

    return LessEqual(x * x, Max(m * m, M * M))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)
    M = Symbol.M(real=True)
    Eq << apply(Contains(x, Interval(m, M)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << algebra.ge.le.imply.le.square.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

