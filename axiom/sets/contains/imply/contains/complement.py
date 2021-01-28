from axiom.utility import prove, apply
from sympy import *
import axiom

from axiom import sets

@apply(imply=True)
def apply(given, U):
    e, domain = axiom.is_Contains(given)
    S, s = axiom.is_Complement(domain)
    assert S in U    
    return Contains(e, U - s)




@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    U = Symbol.U(etype=dtype.integer)
    A = Symbol.A(etype=dtype.integer)
    S = Symbol.S(definition=A & U)
    s = Symbol.s(etype=dtype.integer)
    
    Eq << apply(Contains(x, S - s), U)

    Eq << Subset(Eq[1].rhs, Eq[2].rhs, plausible=True)

    Eq << sets.contains.subset.imply.contains.apply(Eq[1], Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)

