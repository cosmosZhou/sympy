from axiom.utility import prove, apply
from sympy.core.relational import GreaterThan, LessThan
from sympy import Symbol
import axiom
from axiom import algebre


@apply(imply=True)
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = axiom.is_GreaterThan(b_greater_than_x)    
    _x, a = axiom.is_GreaterThan(x_greater_than_a)
    assert x == _x
    return LessThan(a, b)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, x >= a)
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].reversed
       
    
    
if __name__ == '__main__':
    prove(__file__)
