from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(*given):
    x_less_than_y, x_greater_than_y_minus = given
    x, y = axiom.is_Less(x_less_than_y)    
    _x, _y = axiom.is_Greater(x_greater_than_y_minus)
    assert x == _x
    assert y + _y == 0
    return Less(abs(x), abs(y))


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)

    Eq << apply(x < y, x > -y)
    
    Eq << algebra.lt.gt.imply.gt.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1] + y
    
    Eq << Eq[-1] / 2
    
    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[-1])
    
    Eq << algebra.lt.gt.imply.lt.abs.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1] + Eq[-2].reversed
    
    Eq << Eq[-1].this.apply(algebra.lt.simplify.common_terms)
    
if __name__ == '__main__':
    prove()
