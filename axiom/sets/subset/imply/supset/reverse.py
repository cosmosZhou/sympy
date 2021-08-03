from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Supset(B, A)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << sets.supset.given.all_contains.apply(Eq[1])

    Eq << sets.subset.imply.all_contains.apply(Eq[0])


if __name__ == '__main__':
    run()