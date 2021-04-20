from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = axiom.is_Less(a_less_than_x)    
    _x, b = axiom.is_Less(x_less_than_b)
    if b == a:
        a, x, _x, b = _x, b, a, x    
    assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a < x, x < b)
    
    Eq << Eq[0] + Eq[1]   
    
    Eq << Eq[-1].this.apply(algebra.lt.simplify.common_terms)
        
if __name__ == '__main__':
    prove()
