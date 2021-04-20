from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(*given):
    is_positive_x, is_nonnegative_y = given
    x = axiom.is_nonnegative(is_positive_x)
    y = axiom.is_nonnegative(is_nonnegative_y)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(x >= 0, y >= 0)
    
    Eq.case0 = Sufficient(Equal(x, 0), x * y >= 0, plausible=True)
    
    Eq << Eq.case0.this.apply(algebra.sufficient.subs)
    
    Eq << algebra.cond.imply.sufficient.apply(Eq[1], cond=x > 0)
    
    Eq << algebra.sufficient.imply.sufficient.et.apply(Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebra.is_positive.is_nonnegative.imply.is_nonnegative)
    
    Eq <<= Eq.case0 & Eq[-1]
    
    Eq << algebra.cond.sufficient.imply.cond.transit.apply(Eq[0], Eq[-1])

    
if __name__ == '__main__':
    prove()
