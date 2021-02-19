from axiom.utility import prove, apply
from sympy.core.relational import LessThan
from sympy import Symbol
from axiom import algebre
import axiom
from sympy.functions.elementary.piecewise import Piecewise


@apply
def apply(*given):
    x_less_than_y, x_greater_than_y_minus = given
    x, y = axiom.is_LessThan(x_less_than_y)    
    x, _y = axiom.is_GreaterThan(x_greater_than_y_minus)
    assert y + _y == 0
    return LessThan(abs(x), abs(y))


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)

    Eq << apply(x <= y, x >= -y)
    
    Eq << algebre.less_than.greater_than.imply.greater_than.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1] + y
    
    Eq << Eq[-1] / 2
    
    Eq << algebre.is_nonnegative.imply.equal.abs.apply(Eq[-1])
    
    Eq << algebre.less_than.greater_than.imply.less_than.abs.lhs.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1] + Eq[-2].reversed
    
if __name__ == '__main__':
    prove(__file__)
