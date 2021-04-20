from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_Greater(given)
    
    b0, e0 = axiom.is_Pow(lhs)
    b1, e1 = axiom.is_Pow(rhs)
    assert e0.is_even
    assert e1.is_even
    
    e0 //= 2    
    e1 //= 2
    
    return Greater(abs(b0 ** e0), abs(b1 ** e1))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(Greater(x * x, y * y))
    
    Eq << algebra.lt.imply.lt.sqrt.apply(Eq[0].reversed)

    Eq << Eq[-1].reversed
    
if __name__ == '__main__':
    prove()

