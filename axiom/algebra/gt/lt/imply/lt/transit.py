from axiom.utility import prove, apply
from sympy.core.relational import LessEqual, GreaterEqual, Less
from sympy import Symbol
from axiom import algebra
import axiom


@apply
def apply(*given):
    b_greater_than_x, a_less_than_x = given
    b, x = axiom.is_GreaterEqual(b_greater_than_x)    
    a, _x = axiom.is_Less(a_less_than_x)
    assert x == _x
    return Less(a, b)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b >= x, a < x)
    
    Eq << Eq[1].reversed
    
    Eq << algebra.ge.gt.imply.gt.transit.apply(Eq[0], Eq[-1])
    
    Eq << Eq[-1].reversed
      
       
    
    
if __name__ == '__main__':
    prove()
