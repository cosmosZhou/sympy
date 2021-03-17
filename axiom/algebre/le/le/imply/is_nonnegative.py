from axiom.utility import prove, apply
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
import axiom


@apply
def apply(*given):
    less_than_0, less_than_1 = given
    x, a = axiom.is_LessThan(less_than_0)
    y, b = axiom.is_LessThan(less_than_1)
    
    return GreaterThan((x - a) * (y - b), 0)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x <= a, y <= b)   
    
    Eq << Eq[0] - a
    
    Eq << Eq[1] - b
    
    Eq << Eq[-1] * Eq[-2]

    
if __name__ == '__main__':
    prove(__file__)
