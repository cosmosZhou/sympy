from util import *


@apply
def apply(given):
    A, B = given.of(Contains)

    return Equal({A} & B, {A})


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol.e(integer=True)
    s = Symbol.s(etype=dtype.integer)
    Eq << apply(Contains(e, s))

    Eq << sets.contains.imply.subset.apply(Eq[0], simplify=False)

    Eq << sets.subset.imply.eq.intersection.apply(Eq[-1])


if __name__ == '__main__':
    run()

