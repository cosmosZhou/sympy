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

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b), a.emptySet))

    Eq << ~Eq[1]

    Eq << Eq[-1] + a

    Eq << sets.lt.imply.eq.emptySet.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
