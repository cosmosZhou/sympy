from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    eqs = axiom.is_Or(given)
    
    args = []
    for eq in eqs:        
        args.append(axiom.is_zero(eq))
    
    return Equal(Mul(*args), 0)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Equal(a, 0) | Equal(b, 0))
    
    Eq << algebra.is_zero.imply.ou.apply(Eq[1])
    

if __name__ == '__main__':
    prove()
