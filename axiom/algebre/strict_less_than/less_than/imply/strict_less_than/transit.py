from axiom.utility import prove, apply
from sympy.core.relational import LessThan, StrictLessThan
from sympy import Symbol
import axiom


@apply(imply=True)
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = axiom.is_StrictLessThan(a_less_than_x)    
    _x, b = axiom.is_LessThan(x_less_than_b)
    assert x == _x
    return StrictLessThan(a, b)




@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a < x, x <= b)
    
    Eq << Eq[0] + Eq[1]   
    
    
if __name__ == '__main__':
    prove(__file__)
