from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = axiom.is_GreaterThan(x_less_than_y)    
    a, b = axiom.is_GreaterThan(a_less_than_b)
    return GreaterThan(Max(x, a), Max(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x >= y, a >= b)
    
    Eq << GreaterThan(Max(x, a), x, plausible=True)
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.transit.apply(Eq[-1], Eq[0])
    
    Eq << GreaterThan(Max(x, a), a, plausible=True)
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.transit.apply(Eq[1], Eq[-1])
    
    Eq << algebre.greater_than.greater_than.imply.greater_than.max.rhs.apply(Eq[-1], Eq[-3])
    
if __name__ == '__main__':
    prove(__file__)
