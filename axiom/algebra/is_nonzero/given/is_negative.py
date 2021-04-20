from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    x = axiom.is_nonzero(given)    
    return x < 0


@prove
def prove(Eq):
    a = Symbol.a(real=True)    
    Eq << apply(Unequal(a, 0))
    
    Eq << algebra.is_negative.imply.is_nonzero.apply(Eq[1])
    

if __name__ == '__main__':
    prove()
