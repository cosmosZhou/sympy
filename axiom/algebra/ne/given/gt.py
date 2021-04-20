from axiom.utility import prove, apply
from sympy import *
import axiom


@apply
def apply(given):
    lhs, rhs = axiom.is_Unequal(given)
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    Eq << apply(Unequal(x, y))
    
    Eq << ~Eq[0]
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq <<= Eq[1] & Eq[-1]
    

if __name__ == '__main__':
    prove()

