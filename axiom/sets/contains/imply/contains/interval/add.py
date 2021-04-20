from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
def apply(given, t):
    assert given.is_Contains    
    
    e, interval = given.args    
    
    a, b = interval.args
        
    return Contains(e + t, interval.copy(start=a + t, stop=b + t))


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)
    
    Eq << apply(Contains(x, Interval(a, b)), t)
    
    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    
    Eq <<= Eq[-1] + t, Eq[-2] + t
    
    Eq << sets.le.ge.imply.contains.apply(Eq[-1], Eq[-2])

    
if __name__ == '__main__':
    prove()

