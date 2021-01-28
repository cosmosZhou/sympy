from axiom.utility import prove, apply
from sympy import *
from axiom import algebre, sets
import axiom


@apply(imply=True)
def apply(given, S):
    lhs, rhs = axiom.is_Supset(given)    
    return Supset(lhs | S, rhs)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)
   
    Eq << apply(Supset(A, B), S)

    Eq << Eq[0].reversed
    
    Eq << sets.subset.imply.subset.amplify.apply(Eq[-1], S)
    
    Eq << Eq[-1].reversed
        
if __name__ == '__main__':
    prove(__file__)

