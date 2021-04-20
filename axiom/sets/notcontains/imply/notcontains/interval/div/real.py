from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given, d):
     
    d = sympify(d)   
    assert d.is_positive
    
    e, interval = axiom.is_NotContains(given)    
    
    assert interval.is_Interval
    a, b = interval.args
        
    return NotContains(e / d, interval.copy(start=a / d, stop=b / d))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
#     t = Symbol.t(real=True)
    d = Symbol.d(real=True, given=True, positive=True)
    
    Eq << apply(NotContains(x, Interval(a, b)), d)
    
    Eq << ~Eq[-1]
    
    Eq << sets.contains.imply.contains.interval.mul.apply(Eq[-1], d)

    Eq <<= Eq[-1] & Eq[0]
    
if __name__ == '__main__':
    prove()

