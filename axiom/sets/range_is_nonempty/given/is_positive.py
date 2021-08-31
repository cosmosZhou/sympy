from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Greater(b - a, 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << algebra.is_positive.imply.gt.apply(Eq[-1])

    Eq << sets.gt.imply.range_is_nonempty.apply(Eq[-1])



if __name__ == '__main__':
    run()