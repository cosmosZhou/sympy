from axiom.utility import prove, apply
from sympy import *

from axiom import algebra, sets
import axiom


@apply
def apply(given, index=0):
    union, rhs = axiom.is_Subset(given)
    union = axiom.is_Union(union)
        
    return Subset(union[index], rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)
   
    Eq << apply(Subset(A | B, S))
    
    Eq << Subset(A, A | B, plausible=True)
    
    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[0])

    
if __name__ == '__main__':
    prove()

