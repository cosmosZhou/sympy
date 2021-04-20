from sympy import *
from axiom.utility import prove, apply

import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    is_positive_x, is_nonpositive_y = given
    x = axiom.is_positive(is_positive_x)
    y = axiom.is_nonpositive(is_nonpositive_y)
    return LessEqual(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x > 0, y <= 0)
    
    Eq.case0 = Sufficient(Equal(y, 0), Eq[-1], plausible=True)
    
    Eq << Eq.case0.this.apply(algebra.sufficient.subs)
    
    Eq << algebra.cond.imply.sufficient.apply(Eq[0], cond=y < 0)
    
    Eq << algebra.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebra.is_positive.is_negative.imply.is_negative)
    
    Eq << Eq[-1].this.rhs.apply(algebra.is_negative.imply.is_nonpositive)
    
    Eq <<= Eq.case0 & Eq[-1]
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[1], Eq[-1])
    
    
if __name__ == '__main__':
    prove()

