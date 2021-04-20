from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets
# given : A & B = A | B => A = B


@apply(simplify=False)
def apply(given):
    x, a = axiom.is_Equal(given)    
    return Contains(x, a.set) 


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    
    Eq << apply(Equal(x, a))
    
    Eq << Eq[1].simplify()
    


if __name__ == '__main__':
    prove()

