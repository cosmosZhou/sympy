from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    x_less_than_y, a_less_than_b = given
    x, y = axiom.is_Greater(x_less_than_y)    
    a, b = axiom.is_Greater(a_less_than_b)
    return Greater(Max(x, a), Max(y, b))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    
    Eq << apply(x > y, a > b)
    
    Eq << GreaterEqual(Max(x, a), x, plausible=True)
    
    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[-1], Eq[0])
    
    Eq << GreaterEqual(Max(x, a), a, plausible=True)
    
    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[1], Eq[-1])
    
    Eq << algebra.gt.gt.imply.gt.max.rhs.apply(Eq[-1], Eq[-3])
    
if __name__ == '__main__':
    prove()
