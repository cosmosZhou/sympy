from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    x_less_than_b, a_less_than_x = given
    a, x = axiom.is_Equal(a_less_than_x)    
    b, y = axiom.is_GreaterEqual(x_less_than_b)

    return GreaterEqual(a + b, x + y)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(y >= b, Equal(a, x))
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << Eq[-1] - x
    
    
    
if __name__ == '__main__':
    prove()
