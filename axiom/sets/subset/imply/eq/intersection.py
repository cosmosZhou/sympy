from axiom.utility import prove, apply
from sympy import *
from axiom import sets


# given: A in B
# A | B = B
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equal(A & B, A)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Subset(A, B))
    
    Eq << sets.subset.imply.subset.intersect.apply(Eq[0], A)
    
    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove()

