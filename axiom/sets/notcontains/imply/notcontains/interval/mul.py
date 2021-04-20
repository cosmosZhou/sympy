from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given, d):
    e, interval = axiom.is_NotContains(given)
    d = sympify(d)   
    assert d.is_positive
    
    assert interval.is_Interval
    a, b = interval.args
    
    e *= d
    
    return NotContains(e, interval.copy(start=a * d, stop=b * d))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    d = Symbol.d(real=True, positive=True, given=True)

    Eq << apply(NotContains(x, Interval(a, b, right_open=True)), d)

    Eq << ~Eq[-1]
    
    Eq << sets.contains.imply.contains.interval.div.real.apply(Eq[-1], d)
    
    Eq <<= Eq[-1] & Eq[0]
    
if __name__ == '__main__':
    prove()

