from axiom.utility import prove, apply
from sympy.core.relational import LessThan, GreaterThan
from sympy import Symbol
import axiom


@apply(imply=True)
def apply(*given):
    greater_than, less_than = given
    x, a = axiom.is_GreaterThan(greater_than)
    y, b = axiom.is_GreaterThan(less_than)
    
    return GreaterThan((x - a) * (y - b), 0)




@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x >= a, y >= b)   
    
    Eq << Eq[0] - a
    
    Eq << Eq[1] - b
    
    Eq << Eq[-1]* Eq[-2]
    
if __name__ == '__main__':
    prove(__file__)
