from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given, t):
    e, interval = axiom.is_NotContains(given)    
    
    a, b = interval.args
        
    return NotContains(e + t, interval.copy(start=a + t, stop=b + t))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    t = Symbol.t(real=True, given=True)
    
    Eq << apply(NotContains(x, Interval(a, b)), t)
    
    Eq << ~Eq[-1]
    
    Eq << sets.contains.imply.contains.interval.sub.apply(Eq[-1], t)
    
    Eq <<= Eq[-1] & Eq[0]
    

    
if __name__ == '__main__':
    prove()

