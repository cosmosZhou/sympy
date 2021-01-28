from axiom.utility import prove, apply
from sympy import *


# given: A in B
# A | B = B
@apply(imply=True)
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(A | B, B)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    subset = Subset(A, B)

    Eq << apply(subset)
    
    Eq << Subset(B, B, plausible=True)
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << Supset(*Eq[-1].args, plausible=True)
    
    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    prove(__file__)

