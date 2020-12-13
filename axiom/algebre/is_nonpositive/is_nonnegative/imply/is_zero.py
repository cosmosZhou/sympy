from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol
import axiom


@plausible
def apply(*given):
    is_nonpositive, is_nonnegative = given
    x = axiom.is_nonnegative(is_nonnegative)
    _x = axiom.is_nonpositive(is_nonpositive)
    assert x == _x
    return Equality(x, 0)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x <= 0, x >= 0)
    
    Eq <<= Eq[0] & Eq[1]   
    
    Eq << Eq[-1].simplify()
        
    
if __name__ == '__main__':
    prove(__file__)
