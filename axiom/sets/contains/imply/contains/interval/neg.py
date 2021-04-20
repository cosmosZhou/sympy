from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra


@apply
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
    
    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])    

    Eq <<= Eq[-1].reversed, Eq[-2].reversed
    
    Eq << sets.contains.given.et.split.interval.apply(Eq[1])    
    
    Eq << algebra.et.given.cond.apply(Eq[-1])

    
if __name__ == '__main__':
    prove()

