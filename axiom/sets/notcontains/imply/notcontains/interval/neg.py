from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
    e, interval = axiom.is_NotContains(given)    
    
    return NotContains(-e, -interval)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(NotContains(x, Interval(a, b)))
    
    Eq << ~Eq[-1]
    
    Eq << sets.contains.imply.contains.interval.neg.apply(Eq[-1])    
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove()

