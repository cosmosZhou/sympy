from sympy import *
from axiom.utility import prove, apply
from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_Contains    
    
    e, interval = given.args    
    
    return Contains(-e, -interval)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))
    
    Eq << sets.contains.imply.et.interval.apply(Eq[0]).split()    

    Eq <<= -Eq[-1], -Eq[-2]
    
    Eq << sets.contains.given.et.apply(Eq[1]).split()    

    
if __name__ == '__main__':
    prove(__file__)

