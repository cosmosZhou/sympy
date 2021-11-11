from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(b, a)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Equal(Range(a, b), a.emptySet))

    Eq << ~Eq[-1]

    Eq << sets.gt.imply.range_ne_empty.apply(Eq[-1])
    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-06-18
# updated on 2021-06-18
