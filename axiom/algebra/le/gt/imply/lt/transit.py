from axiom.utility import prove, apply
from sympy.core.relational import LessEqual, Less
from sympy import Symbol
from axiom import algebra
import axiom


@apply
def apply(*given):
    a_less_than_x, b_greater_than_x = given
    a, x = axiom.is_LessEqual(a_less_than_x)    
    b, _x = axiom.is_Greater(b_greater_than_x)
    if x != _x:
        x, a, _x, b = b, _x, a, x        
    assert x == _x
    return Less(a, b)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, b > x)
    
    Eq << Eq[1].reversed
    
    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[-1])
    
    
if __name__ == '__main__':
    prove()
