from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply
def apply(given, d):
    assert given.is_Contains 
    d = sympify(d)   
    assert d.is_positive
    assert d.is_integer
    
    e, interval = given.args    
    
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
            
    return Contains(e, Interval(start=ceiling(a / d), stop=b // d, integer=True))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    
    d = Symbol.d(integer=True, positive=True)

    Eq << apply(Contains(d * x, Interval(a, b, integer=True)), d)
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0])
    
    Eq << algebre.et.imply.cond.apply(Eq[-1])
    
    Eq <<= Eq[-1] / d, Eq[-2] / d
    
    Eq <<= algebre.ge.imply.ge.ceiling.apply(Eq[-2]), algebre.le.imply.le.floor.apply(Eq[-1])
    
    Eq << sets.ge.le.imply.contains.apply(Eq[-2], Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)

