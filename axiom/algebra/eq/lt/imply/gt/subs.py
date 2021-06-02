from util import *
import axiom

from axiom.algebra.eq.le.imply.le.subs import ratsimp


@apply
def apply(*given): 
    equal, less_than = given
    assert equal.is_Equal
    assert less_than.is_Less
 
    lhs, rhs, k = ratsimp(equal, less_than)
    assert k < 0
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    b = Symbol.b(real=True)
    k = Symbol.k(real=True, negative=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(Equal(y, x * k + b), x < t)
    
    Eq << Eq[1] * k + b
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    
if __name__ == '__main__':
    run()
