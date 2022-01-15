from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Less(a, b)


@prove
def prove(Eq):
    from axiom import sets
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << sets.range_ne_empty.imply.gt.apply(Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-19
