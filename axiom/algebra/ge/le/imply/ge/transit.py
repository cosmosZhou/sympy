from axiom.utility import prove, apply
from sympy.core.relational import GreaterEqual
from sympy import Symbol
from axiom import algebra
import axiom


@apply
def apply(*given):
    b_greater_than_x, a_less_than_x = given
    b, x = axiom.is_GreaterEqual(b_greater_than_x)    
    a, _x = axiom.is_LessEqual(a_less_than_x)
    if x != _x:
        x, b, _x, a = a, _x, b, x
    assert x == _x
              
    return GreaterEqual(b, a)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, a <= x)
    
    Eq << Eq[1].reversed
    
    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[0], Eq[-1])
    
    
if __name__ == '__main__':
    prove()
