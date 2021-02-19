from axiom.utility import prove, apply
from sympy.core.relational import StrictGreaterThan
from sympy import Symbol
from axiom import algebre
import axiom


@apply
def apply(*given):
    a_less_than_x, b_greater_than_x = given
    a, x = axiom.is_StrictLessThan(a_less_than_x)    
    b, _x = axiom.is_GreaterThan(b_greater_than_x)
    assert x == _x
    return StrictGreaterThan(b, a)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a < x, b >= x)
    
    Eq << Eq[1].reversed
    
    Eq << algebre.strict_less_than.less_than.imply.strict_less_than.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].reversed
    
       
    
    
if __name__ == '__main__':
    prove(__file__)
