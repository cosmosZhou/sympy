from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    equal, notcontains = axiom.is_Or(given)
    
    x, b = axiom.is_Equal(equal)
    _x, ab = axiom.is_NotContains(notcontains)
    assert x == _x
    assert ab.is_Interval
    assert not ab.right_open
    assert b == ab.stop
    ab = ab.copy(right_open=True)
    return NotContains(x, ab)            


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(Equal(x, b) | NotContains(x, Interval(a, b)))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << algebra.et.imply.ou.apply(Eq[-1])
    
        
if __name__ == '__main__':
    prove()

