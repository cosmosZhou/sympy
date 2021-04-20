from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = axiom.is_GreaterEqual(a_less_than_x)    
    b, y = axiom.is_GreaterEqual(x_less_than_b)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(a >= x, y >= b)
    
    Eq << Eq[0] + y
    
    Eq << Eq[1] + x
    
    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[-2], Eq[-1])
    
    
    
if __name__ == '__main__':
    prove()
