from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = axiom.is_Greater(b_greater_than_x)    
    _x, a = axiom.is_GreaterEqual(x_greater_than_a)
    if b == a:
        b, x, _x, a = _x, a, b, x
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(b > x, x >= a)
    
    Eq << ~Eq[-1]
    
    Eq << algebra.ge.le.imply.le.transit.apply(Eq[1], Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
      
    
    
if __name__ == '__main__':
    prove()
