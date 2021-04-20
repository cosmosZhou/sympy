
from sympy.core.relational import Unequal, Greater, \
    GreaterEqual

from axiom.utility import prove, apply
from sympy import Symbol
from sympy.stats.symbolic_probability import Probability as P


# given: x | y = x
# imply: y | x = y
@apply
def apply(given):
    assert given.is_Unequal
    assert given.lhs.is_Probability
    assert given.rhs.is_zero
        
    return Greater(given.lhs, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
 
    Eq << apply(Unequal(P(x), 0))
    
    Eq << GreaterEqual(P(x), 0, plausible=True)
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove()
