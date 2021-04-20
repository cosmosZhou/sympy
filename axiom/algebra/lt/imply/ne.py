from axiom.utility import prove, apply
from sympy import *
import axiom


@apply
def apply(given):
    return Unequal(*axiom.is_Less(given))


@prove
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    Eq << apply(x < y)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[0].subs(Eq[-1])
    

if __name__ == '__main__':
    prove()
