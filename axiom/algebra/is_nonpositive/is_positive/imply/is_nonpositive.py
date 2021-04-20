from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    is_nonpositive_y, is_positive_x = given
    x = axiom.is_positive(is_positive_x)
    y = axiom.is_nonpositive(is_nonpositive_y)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(y <= 0, x > 0)
    
    Eq << algebra.is_positive.is_nonpositive.imply.is_nonpositive.apply(Eq[1], Eq[0])
    
if __name__ == '__main__':
    prove()
