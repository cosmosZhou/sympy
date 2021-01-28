from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets
@apply(imply=True)
def apply(given):
    e, domain = axiom.is_Contains(given)
    S, s = axiom.is_Complement(domain)    
    return Contains(e, S)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    U = Symbol.U(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(Contains(x, U - s))
    
    Eq << Subset(Eq[0].rhs, Eq[1].rhs, plausible=True)
    
    Eq << sets.contains.subset.imply.contains.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

