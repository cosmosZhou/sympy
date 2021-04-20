from axiom.utility import prove, apply
from sympy.core.relational import LessEqual, GreaterEqual, Greater
from sympy import Symbol
import axiom
from axiom import algebra


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = axiom.is_LessEqual(a_less_than_x)    
    _x, b = axiom.is_Less(x_less_than_b)
    assert x == _x
    return Greater(b, a)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, x < b)
    
    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])
    
    Eq << Eq[-1].reversed        
    
    
if __name__ == '__main__':
    prove()
