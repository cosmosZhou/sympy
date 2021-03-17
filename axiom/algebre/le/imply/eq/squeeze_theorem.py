from sympy import *
from axiom.utility import prove, apply
import axiom


@apply
def apply(given):
    x, a = axiom.is_LessThan(given)
    assert x >= a
    return Equality(x, a)


@prove
def prove(Eq):
    x = Symbol.x(domain=Interval(1, oo))
    
    Eq << apply(LessThan(x, 1))
    
    Eq << GreaterThan(x, 1, plausible=True)
    
    Eq <<= Eq[0] & Eq[2]
    

if __name__ == '__main__':
    prove(__file__)

