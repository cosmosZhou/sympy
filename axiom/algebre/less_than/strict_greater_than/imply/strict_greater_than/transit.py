from axiom.utility import plausible
from sympy.core.relational import LessThan, GreaterThan, StrictGreaterThan
from sympy import Symbol
from axiom import algebre
import axiom


@plausible
def apply(*given):
    a_less_than_x, b_greater_than_x = given
    a, x = axiom.is_LessThan(a_less_than_x)    
    b, _x = axiom.is_StrictGreaterThan(b_greater_than_x)
    assert x == _x
    return StrictGreaterThan(b, a)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, b > x)
    
    Eq << Eq[1].reversed
    
    Eq << algebre.less_than.strict_less_than.imply.strict_less_than.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].reversed
    
       
    
    
if __name__ == '__main__':
    prove(__file__)
