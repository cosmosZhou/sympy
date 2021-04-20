from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    is_positive_x, is_negative_y = given
    x = axiom.is_nonnegative(is_positive_x)
    y = axiom.is_negative(is_negative_y)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x >= 0, y < 0)
    
    Eq << algebra.is_negative.is_nonnegative.imply.is_nonpositive.apply(Eq[1], Eq[0])

    
if __name__ == '__main__':
    prove()
