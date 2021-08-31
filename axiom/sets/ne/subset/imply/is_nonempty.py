from util import *


@apply
def apply(ne, subset, evaluate=False):
    _A, _B = ne.of(Unequal)
    A, B = subset.of(Subset)
    assert A == _A and B == _B or A == _B and B == _A
    return Unequal(B - A, A.etype.emptySet, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Unequal(A, B), Subset(A, B, evaluate=False))

    Eq << ~Eq[-1]

    Eq << sets.eq.imply.eq.union.apply(Eq[-1], A)

    Eq << Subset(B, A | B, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq <<= Eq[-1] & Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

