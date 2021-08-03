from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return Subset(B, A)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << sets.subset.given.all_contains.apply(Eq[1])

    Eq << sets.supset.imply.all_contains.apply(Eq[0])


if __name__ == '__main__':
    run()