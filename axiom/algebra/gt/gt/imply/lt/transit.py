from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = axiom.is_Greater(b_greater_than_x)    
    _x, a = axiom.is_Greater(x_greater_than_a)
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, x > a)
    
    Eq << algebra.gt.gt.imply.gt.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove()
