from axiom.utility import plausible
from sympy.core.relational import GreaterThan
from sympy import Symbol
import axiom


@plausible
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = axiom.is_GreaterThan(b_greater_than_x)    
    _x, a = axiom.is_GreaterThan(x_greater_than_a)
    assert x == _x
    return GreaterThan(b, a)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, x >= a)
    
    Eq << Eq[0] + Eq[1]  
       
    
    
if __name__ == '__main__':
    prove(__file__)
