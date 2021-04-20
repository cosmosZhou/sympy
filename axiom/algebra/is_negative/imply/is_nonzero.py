from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra, sets


@apply
def apply(given):
    x = axiom.is_negative(given)
    return Unequal(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    
    Eq << apply(x < 0)
    
    Eq << ~Eq[1]
    
    Eq <<= Eq[-1] & Eq[0]

    
if __name__ == '__main__':
    prove()
