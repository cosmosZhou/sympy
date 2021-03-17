from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(*given):
    b_greater_than_x, a_less_than_x = given
    b, x = axiom.is_StrictGreaterThan(b_greater_than_x)    
    a, _x = axiom.is_LessThan(a_less_than_x)
    if x != _x:
        b, x, a, _x = _x, a, x, b
    assert x == _x
    return StrictLessThan(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, a <= x)
    
    Eq << Eq[1].reversed
    
    Eq << algebre.gt.ge.imply.gt.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove(__file__)
