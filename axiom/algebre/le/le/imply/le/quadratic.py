from sympy import *
from axiom.utility import prove, apply
from axiom import algebre
import axiom


@apply
def apply(*given):
    x_less_than_1, y_less_than_1 = given
    x, one = axiom.is_LessThan(x_less_than_1)
    assert one.is_One
    y, one = axiom.is_LessThan(y_less_than_1)
    assert one.is_One
    
    assert x >= 0 
    assert y >= 0
    return LessThan(x * x + y * y - 1, x * y)




@prove
def prove(Eq):
    x = Symbol.x(real=True, nonnegative=True)
    y = Symbol.y(real=True, nonnegative=True)

    Eq << apply(x <= 1, y <= 1)   
    
    Eq.is_nonpositive = Eq[-1] - Eq[-1].rhs
    
    Eq << GreaterThan(x, 0, plausible=True)
    
    Eq.le = algebre.ge.le.imply.le.quadratic.apply(Eq[-1], Eq[0], quadratic=Eq.is_nonpositive.lhs)
    
    Eq << GreaterThan(y, 0, plausible=True)
    
    Eq << algebre.ge.le.imply.le.quadratic.apply(Eq[-1], Eq[1], quadratic=Eq.le.rhs.args[0])
    
    Eq << algebre.ge.le.imply.le.quadratic.apply(Eq[-2], Eq[1], quadratic=Eq.le.rhs.args[1])
    
    Eq << algebre.le.le.imply.le.max.apply(Eq[-1], Eq[-2])
    
    Eq << algebre.le.le.imply.le.transit.apply(Eq[-1], Eq.le)
    
    
    
if __name__ == '__main__':
    prove(__file__)
