from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given, d):
    assert given.is_Contains 
    d = sympify(d)   
    assert d.is_positive
    
    e, interval = given.args    
    
    assert interval.is_Interval
    a, b = interval.args
        
    return Contains(e / d, interval.copy(start=a / d, stop=b / d))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
#     t = Symbol.t(real=True)
    d = 2
    Eq << apply(Contains(x, Interval(a, b)), d)
    
    Eq << algebra.et.imply.cond.apply(sets.contains.imply.et.split.interval.apply(Eq[0]))
    
    Eq <<= Eq[-2] / d, Eq[-1] / d
    
    Eq << sets.contains.given.et.split.interval.apply(Eq[1])    
    
    Eq << algebra.et.given.cond.apply(Eq[-1])

    
if __name__ == '__main__':
    prove()

