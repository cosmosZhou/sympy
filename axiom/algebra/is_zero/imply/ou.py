from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    multiply = axiom.is_zero(given)
    args = axiom.is_Mul(multiply)
    
    return Or(*(Equal(arg, 0).simplify() for arg in args))


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(a * b, 0))
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].apply(algebra.is_nonzero.is_nonzero.imply.is_nonzero)
    
    Eq <<= Eq[-1] & Eq[0]
    

if __name__ == '__main__':
    prove()
