from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(*given):
    less_than_0, less_than_1 = given
    x, a = axiom.is_LessEqual(less_than_0)
    y, b = axiom.is_LessEqual(less_than_1)
    
    return GreaterEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    Eq << apply(x <= a, y <= b)   
    
    Eq << Eq[0] - a
    
    Eq << Eq[1] - b
    
    Eq << algebra.is_nonpositive.is_nonpositive.imply.is_nonnegative.apply(Eq[-2], Eq[-1])

    
if __name__ == '__main__':
    prove()
