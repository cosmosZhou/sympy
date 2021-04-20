from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


# given e not in S
@apply
def apply(given):
    assert given.is_NotContains
    n, interval = given.args
    a, b = axiom.is_Interval(interval, integer=False)
    assert b.is_Infinity
    return LessEqual(n, a)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)

    Eq << apply(NotContains(x, Interval(a, oo, left_open=True)))
        
    Eq << ~Eq[0]
    
    Eq <<= Eq[-1] & Eq[1]
    
if __name__ == '__main__':
    prove()

