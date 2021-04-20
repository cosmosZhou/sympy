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
    return Less(abs(x), y)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    x = Symbol.x(real=True)

    Eq << apply(x < y, x > -y)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].apply(algebra.cond.given.ou)
    
    Eq << algebra.cond.given.et.restrict.apply(Eq[-1], cond=Eq[0])
    
    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1])
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq << -Eq[1]
    
    Eq << algebra.cond.given.et.restrict.apply(Eq[-2], cond=Eq[-1])
    
    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1])
    
    
if __name__ == '__main__':
    prove()
    
from . import both
from . import max
