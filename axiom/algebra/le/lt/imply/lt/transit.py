from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    if not a_less_than_x.is_LessEqual:
        x_less_than_b, a_less_than_x = given
        
    a, x = axiom.is_LessEqual(a_less_than_x)    
    _x, b = axiom.is_Less(x_less_than_b)
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    b = Symbol.b(real=True, given=True)

    Eq << apply(a <= x, x < b)
    
    Eq << ~Eq[-1]   
    
    Eq << algebra.le.ge.imply.ge.transit.apply(Eq[0], Eq[-1])
    
    Eq <<= Eq[1] & Eq[-1]
    
    
if __name__ == '__main__':
    prove()
