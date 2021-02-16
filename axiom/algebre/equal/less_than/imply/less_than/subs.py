from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre

def ratsimp(equal, eq):    
    self_lhs, self_rhs = equal.args
    old, new = eq.args
    lhs = self_lhs.subs(old, new)
    rhs = self_rhs.subs(old, new)
    
    delta = (lhs - rhs) - (self_lhs - self_rhs)
    match = old - new

    return lhs, rhs, (delta / match).ratsimp()
    
@apply(imply=True)
def apply(*given): 
    equal, less_than = given    
    assert equal.is_Equal
    assert less_than.is_LessThan
 
    lhs, rhs, k = ratsimp(equal, less_than)
    assert k > 0
    return LessThan(lhs, rhs)


@prove
def prove(Eq):
    y = Symbol.y(real=True)
    b = Symbol.b(real=True)
    k = Symbol.k(real=True, positive=True)
    
    x = Symbol.x(real=True)
    
    t = Symbol.t(real=True)
    
    Eq << apply(Equality(y, x * k + b), x <= t)
    
    Eq << Eq[1] * k + b
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
if __name__ == '__main__':
    prove(__file__)
