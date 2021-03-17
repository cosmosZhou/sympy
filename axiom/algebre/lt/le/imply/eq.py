from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given):
    x1_less_than_y, y_less_than_x = given
    x1, y = axiom.is_StrictLessThan(x1_less_than_y)    
    _y, x = axiom.is_LessThan(y_less_than_x)
    assert y == _y
    assert x1 + 1 == x
    assert y.is_integer
    
    return Equal(y, floor(x))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(integer=True)

    Eq << apply(x - 1 < y, y <= x)
    
    Eq << Eq[0] - y + 1
    
    Eq << (Eq[1] - y).reversed
    
    Eq << algebre.is_nonnegative.lt.imply.eq.frac.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.rhs.definition
    
    
if __name__ == '__main__':
    prove(__file__)
