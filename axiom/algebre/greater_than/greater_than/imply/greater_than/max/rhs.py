from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    x_less_than_y, x_less_than_b = given
    x, y = axiom.is_GreaterThan(x_less_than_y)    
    _x, b = axiom.is_GreaterThan(x_less_than_b)
    assert x == _x
    return GreaterThan(x, Max(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    b = Symbol.b(real=True, given=True)
    
    Eq << apply(x >= y, x >= b)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    Eq << algebre.condition.given.ou.apply(Eq[-1])
    
    Eq << ~Eq[-1]
    
    Eq << algebre.condition.condition.imply.condition.apply(Eq[0], Eq[-1], invert=True, reverse=True)
    
    Eq << algebre.condition.condition.imply.condition.apply(Eq[1], Eq[-1], invert=True, reverse=True)
    
if __name__ == '__main__':
    prove(__file__)
