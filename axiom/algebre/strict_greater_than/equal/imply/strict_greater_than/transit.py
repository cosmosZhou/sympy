from axiom.utility import prove, apply
from sympy.core.relational import StrictGreaterThan, Equality
from sympy import Symbol
import axiom


@apply(imply=True)
def apply(*given):
    b_greater_than_x, x_eq_a = given
    b, x = axiom.is_StrictGreaterThan(b_greater_than_x)    
    _x, a = axiom.is_Equal(x_eq_a)
    assert x == _x
    return StrictGreaterThan(b, a)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(b > x, Equality(x, a))
    
    Eq << Eq[0] + Eq[1]  
    
    
if __name__ == '__main__':
    prove(__file__)
