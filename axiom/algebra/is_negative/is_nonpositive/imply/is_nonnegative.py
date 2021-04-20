from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    is_negative_x, is_nonpositive_y = given
    x = axiom.is_negative(is_negative_x)
    y = axiom.is_nonpositive(is_nonpositive_y)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x < 0, y <= 0)
    
    Eq << -algebra.is_positive.is_nonpositive.imply.is_nonpositive.apply(-Eq[0], Eq[1])
    
    
    
if __name__ == '__main__':
    prove()

