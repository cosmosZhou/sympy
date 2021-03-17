from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre
from axiom.algebre.eq.le.imply.le.subs import ratsimp

@apply
def apply(*given): 
    less_than_f, less_than = given
    assert less_than_f.is_GreaterThan    
    assert less_than.is_GreaterThan
 
    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k > 0
    return GreaterThan(lhs, rhs)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    b = Symbol.b(real=True)
    k = Symbol.k(real=True, positive=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(y >= x * k + b, x >= t)
    
    Eq << Eq[1] * k + b
    
    Eq << algebre.ge.ge.imply.ge.transit.apply(Eq[-1], Eq[0])
    
if __name__ == '__main__':
    prove(__file__)
