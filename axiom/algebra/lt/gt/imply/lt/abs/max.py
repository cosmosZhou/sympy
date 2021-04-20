from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(*given):
    x_less_than_y, x_greater_than_y_minus = given
    x, a = axiom.is_Less(x_less_than_y)    
    _x, b = axiom.is_Greater(x_greater_than_y_minus)
    assert x == _x
    return Less(abs(x), Max(abs(a), abs(b)))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)    
    b = Symbol.b(real=True, given=True)

    Eq << apply(x < a, x > b)
    
    Eq << algebra.lt.given.cond.split.abs.apply(Eq[-1])
    
    Eq <<= ~Eq[-2], -~Eq[-1]
    
    Eq <<= algebra.ge.imply.ge.relaxed.apply(Eq[-2], abs(a)), -algebra.ge.imply.ge.relaxed.apply(Eq[-1], abs(b))
    
    Eq <<= algebra.lt.ge.imply.gt.transit.apply(Eq[0], Eq[-2]), -algebra.gt.le.imply.lt.transit.apply(Eq[1], Eq[-1])
    
    Eq <<= algebra.imply.le.abs.apply(a), algebra.imply.le.abs.apply(b, negate=True)
    
    Eq <<= Eq[-2] & Eq[-4], Eq[-1] & Eq[-3]
    
    
if __name__ == '__main__':
    prove()
