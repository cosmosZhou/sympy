from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return GreaterEqual(b - a, 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b), a.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1] + a

    Eq << sets.lt.imply.interval_is_empty.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-09-23
