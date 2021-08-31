from util import *




@apply
def apply(given, index=0):
    union, rhs = given.of(Subset)
    union = union.of(Union)

    return Subset(union[index], rhs)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex * n)

    Eq << apply(Subset(A | B, S))

    Eq << Subset(A, A | B, plausible=True)

    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

