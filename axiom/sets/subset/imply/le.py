from util import *


@apply
def apply(given):
    A, B = given.of(Subset)

    return LessEqual(Card(A), Card(B))


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Subset(A, B))

    Eq << sets.subset.imply.eq.complement.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << Eq[-1] + Eq[-2].reversed


if __name__ == '__main__':
    run()

