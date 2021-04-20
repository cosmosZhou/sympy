from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):    
    is_nonzero_x, is_nonzero_y = axiom.is_And(given)
    x = axiom.is_nonzero(is_nonzero_x)    
    y = axiom.is_nonzero(is_nonzero_y)    
    return Unequal(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(Unequal(x, 0) & Unequal(y, 0))
    
    Eq << algebra.is_nonzero.imply.et.apply(Eq[1])
    
if __name__ == '__main__':
    prove()
