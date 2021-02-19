from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets
@apply
def apply(given, S):
    lhs, rhs = axiom.is_Subset(given)    
    return Subset(lhs | S, rhs | S)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)
   
    Eq << apply(Subset(A, B), S)
    
    Eq << sets.subset.imply.subset.amplify.apply(Eq[0], S)
    
    Eq << Subset(S, B | S, plausible=True)
    
    Eq <<= Eq[-1] & Eq[-2]
    
if __name__ == '__main__':
    prove(__file__)


