from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given):
    x, b = axiom.is_GreaterEqual(given)
    domain = x.domain
    assert domain.is_Interval
    a, b = domain.args
    assert not domain.right_open
    
    return Equal(x, b)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True, given=True)
    x = Symbol.x(domain=Interval(a, b), given=True)
    
    Eq << apply(x >= b)
    
    Eq << ~Eq[-1] 
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    prove()

