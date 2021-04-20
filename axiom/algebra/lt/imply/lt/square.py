from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    lhs, rhs = axiom.is_Less(given)
    
    assert lhs.is_real
    assert rhs.is_real
    assert lhs >= 0
    
    return Less(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True, nonnegative=True)
    y = Symbol.y(real=True)
    
    Eq << apply(Less(x, y))
    
    Eq << algebra.lt.lt.imply.lt.multiply.apply(Eq[0], Eq[0])
    
    

if __name__ == '__main__':
    prove()

