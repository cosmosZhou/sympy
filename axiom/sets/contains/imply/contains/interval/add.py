from sympy import *
from axiom.utility import prove, apply
from axiom import sets


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
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0]).split()
    
    Eq <<= Eq[-1] + t, Eq[-2] + t
    
    Eq << sets.less_than.greater_than.imply.contains.apply(Eq[-1], Eq[-2])

    
if __name__ == '__main__':
    prove(__file__)

