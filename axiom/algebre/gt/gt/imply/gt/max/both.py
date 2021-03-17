from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = axiom.is_StrictGreaterThan(x_less_than_y)    
    a, b = axiom.is_StrictGreaterThan(a_less_than_b)
    return StrictGreaterThan(Max(x, a), Max(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x > y, a > b)
    
    Eq << GreaterThan(Max(x, a), x, plausible=True)
    
    Eq << algebre.ge.gt.imply.gt.transit.apply(Eq[-1], Eq[0])
    
    Eq << GreaterThan(Max(x, a), a, plausible=True)
    
    Eq << algebre.gt.ge.imply.gt.transit.apply(Eq[1], Eq[-1])
    
    Eq << algebre.gt.gt.imply.gt.max.rhs.apply(Eq[-1], Eq[-3])
    
if __name__ == '__main__':
    prove(__file__)
