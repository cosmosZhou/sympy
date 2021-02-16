from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre
from axiom.algebre.equal.less_than.imply.less_than.subs import ratsimp

@apply(imply=True)
def apply(*given): 
    less_than_f, less_than = given
    assert less_than_f.is_StrictGreaterThan    
    assert less_than.is_LessThan
 
    lhs, rhs, k = ratsimp(less_than_f, less_than)
    assert k < 0
    return StrictGreaterThan(lhs, rhs)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    b = Symbol.b(real=True)
    k = Symbol.k(real=True, positive=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(x * k + b > y, x <= t)

    Eq << Eq[1] * k + b
    
    Eq << algebre.less_than.strict_greater_than.imply.strict_greater_than.transit.apply(Eq[-1], Eq[0])
    
if __name__ == '__main__':
    prove(__file__)
