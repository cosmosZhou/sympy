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

    Eq << sets.interval_ne_empty.imply.ge_zero.apply(Eq[0])

    Eq << Eq[-1] + a


if __name__ == '__main__':
    run()
# created on 2019-09-23
