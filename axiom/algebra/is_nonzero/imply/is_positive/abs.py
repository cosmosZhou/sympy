from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets, algebra


@apply
def apply(given):
    x = axiom.is_nonzero(given)
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True)

    Eq << apply(Unequal(a, 0))
    
    Eq << algebra.is_nonzero.imply.is_nonzero.abs.apply(Eq[0])
    
    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[-1])
    

if __name__ == '__main__':
    prove()
