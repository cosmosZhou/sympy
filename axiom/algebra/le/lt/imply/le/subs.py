from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from axiom.algebra.eq.le.imply.le.subs import ratsimp

@apply
def apply(*given): 
    less_than_f, less_than = given
    if not less_than_f.is_LessEqual:
        less_than, less_than_f = given
        
    assert less_than_f.is_LessEqual    
    assert less_than.is_Less
 
    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k >= 0
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    b = Symbol.b(real=True)
    k = Symbol.k(real=True, nonnegative=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(y <= x * k + b, x < t)
    
    Eq << algebra.lt.imply.le.multiply.apply(Eq[1], k)
    
    Eq << Eq[-1] + b
    
    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq[0])
    
if __name__ == '__main__':
    prove()
