from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    x = axiom.is_nonnegative(given)
    return x > 0


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    
    Eq << apply(x >= 0)
    
    Eq << algebra.is_positive.imply.is_nonnegative.apply(Eq[1])
    
    
if __name__ == '__main__':
    prove()
