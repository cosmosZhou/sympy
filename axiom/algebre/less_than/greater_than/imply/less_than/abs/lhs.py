from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(*given):
    x_less_than_y, x_greater_than_y_minus = given
    x, y = axiom.is_LessThan(x_less_than_y)    
    x, _y = axiom.is_GreaterThan(x_greater_than_y_minus)
    assert y + _y == 0
    return LessThan(abs(x), y)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)

    Eq << apply(x <= y, x >= -y)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].apply(algebre.condition.given.ou)
    
    Eq << algebre.condition.given.et.apply(Eq[-1], Eq[0])
    
    Eq << algebre.et.given.et.subs.apply(Eq[-1])
    
    Eq << Eq[-1].split()
    
    Eq << -Eq[1]
    
    Eq << algebre.condition.given.et.apply(Eq[-2], Eq[-1])
    
    Eq << algebre.et.given.et.subs.apply(Eq[-1])
    
    
if __name__ == '__main__':
    prove(__file__)
