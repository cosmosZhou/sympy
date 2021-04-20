from sympy import *
from axiom.utility import prove, apply
from axiom import algebra
import axiom


@apply
def apply(given):
    is_nonzero, eq = axiom.is_And(given)
    if not eq.is_Equal:
        is_nonzero, eq = eq, is_nonzero
    x = axiom.is_nonzero(is_nonzero)
    a, b = axiom.is_Equal(eq)
    return is_nonzero & Equal((a * x).expand(), (b * x).expand()).simplify() 


@prove
def prove(Eq):
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    z = Symbol.z(integer=True)

    Eq << apply(Equal(1 / x + y, z) & Unequal(x, 0))
            
    Eq << Eq[-1].apply(algebra.is_nonzero.eq.imply.eq.divide)
    
    Eq << algebra.et.imply.cond.apply(Eq[1], index=0)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    
if __name__ == '__main__':
    prove()

