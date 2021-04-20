from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    is_nonpositive, is_nonnegative_y = given
    x = axiom.is_nonpositive(is_nonpositive)
    y = axiom.is_nonnegative(is_nonnegative_y)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x <= 0, y >= 0)
    
    Eq.is_zero = Sufficient(Equal(x, 0) & (y >= 0), x * y <= 0, plausible=True)
    
    Eq << Eq.is_zero.this.lhs.apply(algebra.et.imply.cond, index=0)
    
    Eq << Eq[-1].this.lhs * y
    
    Eq << algebra.sufficient.given.ou.apply(Eq[-1])
    
    Eq.is_negative = Sufficient((x < 0) & (y >= 0), x * y <= 0, plausible=True)
    
    Eq << Eq.is_negative.this.lhs.apply(algebra.is_negative.is_nonnegative.imply.is_nonpositive)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.ou.apply(Eq.is_zero, Eq.is_negative)
    
    Eq <<= Eq[0] & Eq[1]
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[-1], Eq[-2])

    
if __name__ == '__main__':
    prove()
