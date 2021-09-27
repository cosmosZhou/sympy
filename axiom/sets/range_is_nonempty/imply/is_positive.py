from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b - a, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << sets.range_is_nonempty.imply.gt.apply(Eq[0])
    Eq << algebra.gt.imply.is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()