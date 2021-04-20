from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):    
    x_less_than_y, x_less_than_b = axiom.is_And(given)
    x, y = axiom.is_Greater(x_less_than_y)    
    _x, b = axiom.is_Greater(x_less_than_b)
    assert x == _x
    return Greater(x, Max(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    b = Symbol.b(real=True, given=True)
    
    Eq << apply((x > y) & (x > b))
    
    Eq << algebra.et.given.cond.apply(Eq[0])
    
    Eq << algebra.gt.imply.gt.relaxed.apply(Eq[1], b)
    
    Eq << algebra.gt.imply.gt.relaxed.apply(Eq[1], y)
    
if __name__ == '__main__':
    prove()
