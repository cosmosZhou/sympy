from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    a_less_than_b, x_less_than_y = given
    a, b = axiom.is_Greater(a_less_than_b)    
    x, y = axiom.is_Greater(x_less_than_y)
    
    assert b.is_nonnegative
    assert y.is_nonnegative
    return Greater(a * x, b * y)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True, nonnegative=True)
    y = Symbol.y(real=True, nonnegative=True)

    Eq << apply(a > b, x > y)
    
    Eq << algebra.lt.lt.imply.lt.multiply.apply(Eq[0].reversed, Eq[1].reversed)
    
    Eq << Eq[-1].reversed
    
    
if __name__ == '__main__':
    prove()
