from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    x = axiom.is_positive(given)
    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
        
    Eq << apply(x > 0)
    
    Eq << algebra.gt.imply.ge.relax.apply(Eq[0])

    
if __name__ == '__main__':
    prove()

