from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra
from axiom.algebra.eq.le.imply.le.subs import ratsimp

@apply
def apply(*given): 
    less_than_f, less_than = given
    assert less_than_f.is_Greater    
    assert less_than.is_LessEqual
 
    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k < 0
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    b = Symbol.b(real=True)
    k = Symbol.k(real=True, positive=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(x * k + b > y, x <= t)

    Eq << Eq[1] * k + b
    
    Eq << algebra.le.gt.imply.gt.transit.apply(Eq[-1], Eq[0])
    
if __name__ == '__main__':
    prove()
