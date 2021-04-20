from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given):
    a_less_than_b, x_less_than_y = given
    a, b = axiom.is_Less(a_less_than_b)    
    x, y = axiom.is_Less(x_less_than_y)
    
    assert a.is_nonnegative
    assert x.is_nonnegative
    return Less(a * x, b * y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, nonnegative=True)
    x = Symbol.x(real=True, nonnegative=True)
    b = Symbol.b(real=True)
    y = Symbol.y(real=True)

    Eq << apply(a < b, x < y)
    
    Eq << Eq[2] - x * b
    
    Eq << Eq[-1].this.lhs.collect(x)
    
    Eq << Eq[-1].this.rhs.collect(b)
    
    Eq << Eq[0].reversed
    
    Eq << algebra.gt.imply.gt.relaxed.apply(Eq[-1], 0)
    
    Eq << Eq[1] - x
    
    Eq.is_positive = algebra.is_positive.is_positive.imply.is_positive.mul.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[0] - a
    
    Eq << -Eq[-1]
    
    Eq << GreaterEqual(x, 0, plausible=True)
    
    Eq << algebra.is_negative.is_nonnegative.imply.is_nonpositive.apply(Eq[-2], Eq[-1])
    
    Eq << algebra.gt.le.imply.lt.transit.apply(Eq.is_positive, Eq[-1])
       
    
    
if __name__ == '__main__':
    prove()
