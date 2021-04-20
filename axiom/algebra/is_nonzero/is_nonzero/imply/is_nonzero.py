from axiom.utility import prove, apply
from sympy import *

import axiom
from axiom import algebra


@apply
def apply(*given):
    is_nonzero_x, is_nonzero_y = given
    x = axiom.is_nonzero(is_nonzero_x)
    y = axiom.is_nonzero(is_nonzero_y)
    return Unequal(x * y, 0)


@prove
def prove(Eq): 
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))
    
    Eq << algebra.is_nonzero.imply.is_positive.abs.apply(Eq[0])
    
    Eq << algebra.is_nonzero.imply.is_positive.abs.apply(Eq[1])
    
    Eq << algebra.is_positive.is_positive.imply.is_positive.mul.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.abs)
    
    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[-1])
    
    Eq << algebra.is_nonzero.imply.is_nonzero.strip.abs.apply(Eq[-1])
    
    

        
if __name__ == '__main__':
    prove()
