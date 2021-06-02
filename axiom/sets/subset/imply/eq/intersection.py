from util import *



# given: A in B
# A | B = B
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equal(A & B, A)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Subset(A, B))

    Eq << sets.subset.imply.subset.intersection.apply(Eq[0], A)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
