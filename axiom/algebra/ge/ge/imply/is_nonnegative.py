from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    greater_than, less_than = given
    x, a = axiom.is_GreaterEqual(greater_than)
    y, b = axiom.is_GreaterEqual(less_than)
    
    return GreaterEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x >= a, y >= b)   
    
    Eq << Eq[0] - a
    
    Eq << Eq[1] - b
    
    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.apply(Eq[-1], Eq[-2])

    
if __name__ == '__main__':
    prove()
