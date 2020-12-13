from axiom.utility import plausible
from sympy.sets.contains import Contains, Subset
from sympy import Symbol
import axiom
from sympy.core.symbol import dtype
from axiom import sets


@plausible
def apply(given):
    e, domain = axiom.is_Contains(given)
    S, s = axiom.is_Complement(domain)    
    return Contains(e, S)


from axiom.utility import check


@check
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

