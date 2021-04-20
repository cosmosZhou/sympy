from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(*given):
    b_greater_than_x, x_greater_than_a = given
    b, x = axiom.is_GreaterEqual(b_greater_than_x)    
    _x, a = axiom.is_GreaterEqual(x_greater_than_a)
    if b == a:
        b, x, _x, a = _x, a, b, x    
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, x >= a)
    
    Eq << Eq[0] + Eq[1]  
    
    Eq << Eq[-1] - x
    
    
if __name__ == '__main__':
    prove()
