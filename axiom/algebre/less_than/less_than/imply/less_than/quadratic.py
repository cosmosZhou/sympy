from axiom.utility import plausible
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
from axiom import algebre
import axiom


@plausible
def apply(*given):
    x_less_than_1, y_less_than_1 = given
    x, one = axiom.is_LessThan(x_less_than_1)
    assert one.is_One
    y, one = axiom.is_LessThan(y_less_than_1)
    assert one.is_One
    
    assert x >= 0 
    assert y >= 0
    return LessThan(x * x + y * y - 1, x * y)


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True, nonnegative=True)
    y = Symbol.y(real=True, nonnegative=True)

    Eq << apply(x <= 1, y <= 1)   
    
    Eq.is_nonpositive = Eq[-1] - Eq[-1].rhs
    
    Eq << GreaterThan(x, 0, plausible=True)
    
    Eq.less_than = algebre.greater_than.less_than.imply.less_than.quadratic.apply(Eq[-1], Eq[0], quadratic=Eq.is_nonpositive.lhs)
    
    Eq << GreaterThan(y, 0, plausible=True)
    
    Eq << algebre.greater_than.less_than.imply.less_than.quadratic.apply(Eq[-1], Eq[1], quadratic=Eq.less_than.rhs.args[0])
    
    Eq << algebre.greater_than.less_than.imply.less_than.quadratic.apply(Eq[-2], Eq[1], quadratic=Eq.less_than.rhs.args[1])
    
    Eq << algebre.less_than.less_than.imply.less_than.max.apply(Eq[-1], Eq[-2])
    
    Eq << algebre.less_than.less_than.imply.less_than.transit.apply(Eq[-1], Eq.less_than)
    
    
    
if __name__ == '__main__':
    prove(__file__)
