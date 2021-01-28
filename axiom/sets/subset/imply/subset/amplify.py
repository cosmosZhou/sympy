from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets

@apply(imply=True)
def apply(given, S):
    lhs, rhs = axiom.is_Subset(given)    
    return Subset(lhs, rhs | S)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)
   
    Eq << apply(Subset(A, B), S)

    Eq << Subset(B, B | S, plausible=True)
    
    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[0])
        
if __name__ == '__main__':
    prove(__file__)

