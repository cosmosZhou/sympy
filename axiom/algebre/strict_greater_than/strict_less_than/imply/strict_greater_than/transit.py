from axiom.utility import plausible
from sympy.core.relational import GreaterThan, StrictGreaterThan
from sympy import Symbol
from axiom import algebre
import axiom


@plausible
def apply(*given):
    b_greater_than_x, a_less_than_x = given
    b, x = axiom.is_StrictGreaterThan(b_greater_than_x)    
    a, _x = axiom.is_StrictLessThan(a_less_than_x)
    if x != _x:
        x, b, _x, a = a, _x, b, x
    assert x == _x
              
    return StrictGreaterThan(b, a)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, a < x)
    
    Eq << Eq[1].reversed
    
    Eq << algebre.strict_greater_than.strict_greater_than.imply.strict_greater_than.transit.apply(Eq[0], Eq[-1])
    
    
if __name__ == '__main__':
    prove(__file__)
