from util import *


@apply
def apply(given, reverse=False):
    x, B = given.of(Contains)
    A = x.set | B
    if reverse:
        A, B = B, A

    return Equal(x.set | B, B)


@prove
def prove(Eq):
    from axiom import sets

    e = Symbol.e(integer=True)
    S = Symbol.S(etype=dtype.integer)
    Eq << apply(Contains(e, S))

    Eq << Eq[0].apply(sets.contains.imply.subset, simplify=False)

    Eq << sets.subset.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    run()

