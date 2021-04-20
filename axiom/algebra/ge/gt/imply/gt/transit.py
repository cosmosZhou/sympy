from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = axiom.is_GreaterEqual(b_greater_than_x)    
    _x, a = axiom.is_Greater(x_greater_than_a)
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(b >= x, x > a)
    
    Eq << ~Eq[-1]
    
    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[0], Eq[-1])
    
    Eq <<= Eq[-1] & Eq[1]
    
    
if __name__ == '__main__':
    prove()
