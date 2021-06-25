from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Interval)
    assert A.left_open or A.right_open
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Unequal(Interval(a, b, left_open=True), a.emptySet))

    Eq << sets.interval_is_nonemptyset.imply.is_positive.apply(Eq[0])

    Eq << Eq[-1] + a

    

    


if __name__ == '__main__':
    run()