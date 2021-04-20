from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_GreaterEqual(given)
    
    assert lhs.is_real
    assert rhs.is_real
    assert rhs >= 0
    
    return GreaterEqual(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True, nonnegative=True)
    
    Eq << apply(GreaterEqual(x, y))
    
    Eq << algebra.ge.ge.imply.ge.multiply.apply(Eq[0], Eq[0])
    
    

if __name__ == '__main__':
    prove()

