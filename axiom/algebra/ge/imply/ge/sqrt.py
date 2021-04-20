from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_GreaterEqual(given)
    
    lhs = axiom.is_Square(lhs)
    rhs = axiom.is_Square(rhs)
    
    assert lhs.is_real
    assert rhs.is_real
    
    return GreaterEqual(abs(lhs), abs(rhs))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(GreaterEqual(x * x, y * y))
    
    Eq << algebra.le.imply.le.sqrt.apply(Eq[0].reversed)
    
    Eq << Eq[-1].reversed
    
    

if __name__ == '__main__':
    prove()

