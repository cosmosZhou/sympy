from util import *


@apply
def apply(given, left_open=False, right_open=False):
    a, b = given.of(Less)

    return Equal(Interval(b, a, left_open=left_open, right_open=right_open), a.emptySet)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x < y)

    Eq << Eq[0].reversed
    Eq << sets.gt.imply.eq.emptySet.apply(Eq[-1])


if __name__ == '__main__':
    run()
