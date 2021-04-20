from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets

@apply
def apply(given, index=None):
    e, domain = axiom.is_Contains(given)
    s = axiom.is_Intersection(domain)
    if index is None:
        return tuple(Contains(e, s) for s in s)
    
    return Contains(e, s[index])


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    B = Symbol.B(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    
    Eq << apply(Contains(x, A & B), index=0)
    
    Eq << Subset(A & B, A, plausible=True)
    
    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove()

