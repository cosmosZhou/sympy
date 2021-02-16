from sympy import *
from axiom.utility import prove, apply
import axiom


@apply(imply=True)
def apply(given):
    lhs, rhs = axiom.is_StrictGreaterThan(given)
    
    if lhs.is_integer and rhs.is_integer:
        return GreaterThan(lhs, rhs + 1)
    return GreaterThan(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(x > y)    

    Eq << ~Eq[-1]
    
    Eq <<= Eq[0] & Eq[-1]    

if __name__ == '__main__':
    prove(__file__)
