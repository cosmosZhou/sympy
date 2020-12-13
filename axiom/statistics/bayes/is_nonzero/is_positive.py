
from sympy.core.relational import Unequal, StrictGreaterThan, \
    GreaterThan

from axiom.utility import plausible
from axiom.utility import check
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P


# given: x | y = x
# imply: y | x = y
@plausible
def apply(given):
    assert given.is_Unequality
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
        
    return StrictGreaterThan(given.lhs, 0)


@check
def prove(Eq):
    x = Symbol.x(real=True, random=True)
 
    Eq << apply(Unequal(P(x), 0))
    
    Eq << GreaterThan(P(x), 0, plausible=True)
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove(__file__)
