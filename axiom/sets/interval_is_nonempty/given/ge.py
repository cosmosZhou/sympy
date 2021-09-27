from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert not A.left_open and not A.right_open
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b), a.emptySet))

    Eq << ~Eq[0]

    Eq << sets.interval_is_empty.imply.lt.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
