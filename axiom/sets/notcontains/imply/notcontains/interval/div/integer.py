from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given, d):
     
    d = sympify(d)   
    assert d.is_positive
    assert d.is_integer
    
    e, interval = axiom.is_NotContains(given)    
    
    assert interval.is_Interval
    a, b = interval.args
        
    assert interval.is_integer
    e /= d
    assert e.is_integer
    if interval.left_open:
        a += 1
        if interval.right_open:
            b -= 1
    else:
        if interval.right_open: 
            b -= 1
            
    return NotContains(e, Interval(start=ceiling(a / d), stop=b // d, integer=True))


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    
    d = Symbol.d(integer=True, positive=True, given=True)

    Eq << apply(NotContains(d * x, Interval(a, b, integer=True)), d)
    
    Eq << ~Eq[-1]
    
    Eq.contains = sets.contains.imply.contains.interval.mul.apply(Eq[-1], d)
    
    Eq << algebra.imply.le.floor.apply(b, d)
    
    Eq << algebra.imply.ge.ceiling.apply(a, d)
    
    Eq << sets.le.ge.imply.subset.apply(Eq[-2], Eq[-1])
    
    Eq << sets.contains.subset.imply.contains.apply(Eq.contains, Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]    

    
if __name__ == '__main__':
    prove()

