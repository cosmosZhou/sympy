from util import *


@apply
def apply(given):
    e, S = given.of(NotContains)
    return Equal(abs(S | {e}), abs(S) + 1)


@prove
def prove(Eq):
    from axiom import sets

    S = Symbol.S(etype=dtype.integer)
    e = Symbol.e(integer=True)
    Eq << apply(NotContains(e, S))

    Eq << sets.notcontains.imply.is_emptyset.intersection.apply(Eq[0])

    Eq << sets.intersection_is_emptyset.imply.eq.apply(Eq[-1])


if __name__ == '__main__':
    run()