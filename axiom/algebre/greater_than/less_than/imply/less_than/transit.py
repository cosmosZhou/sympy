from axiom.utility import prove, apply
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
from axiom import algebre
import axiom


@apply(imply=True)
def apply(*given):
    b_greater_than_x, a_less_than_x = given
    b, x = axiom.is_GreaterThan(b_greater_than_x)    
    a, _x = axiom.is_LessThan(a_less_than_x)
    if x != _x:
        b, x, a, _x = _x, a, x, b    
    assert x == _x
    return LessThan(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, a <= x)
    
    Eq << Eq[1].reversed
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove(__file__)
