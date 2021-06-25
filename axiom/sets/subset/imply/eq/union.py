from util import *


# given: A in B
# A | B = B
@apply
def apply(given):
    A, B = given.of(Subset)

    return Equal(A | B, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Subset(B, B, plausible=True)

    Eq <<= Eq[-1] & Eq[0]

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

