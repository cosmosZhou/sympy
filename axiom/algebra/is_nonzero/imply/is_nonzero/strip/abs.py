from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given):
    x = axiom.is_nonzero(given)
    x = axiom.is_Abs(x)
    return Unequal(x, 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)

    Eq << apply(Unequal(abs(a), 0))
    
    Eq << ~Eq[1]
    
    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[-1], Eq[0])    

if __name__ == '__main__':
    prove()
