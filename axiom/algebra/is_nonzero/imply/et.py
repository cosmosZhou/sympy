from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    multiply = axiom.is_nonzero(given)
    args = axiom.is_Mul(multiply)
    return And(*(Unequal(arg, ZeroMatrix(*arg.shape)).simplify() for arg in args))


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Unequal(a * b, 0))
    
    Eq << algebra.et.given.cond.apply(Eq[-1])
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq <<= Eq[0].subs(Eq[-1]), Eq[0].subs(Eq[-2])
    

if __name__ == '__main__':
    prove()
