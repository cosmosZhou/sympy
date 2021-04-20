from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given, reverse=False):
    xy = axiom.is_zero(given)
    x, y = axiom.is_Substract(xy)
    if reverse:
        x, y = y, x
    
    return Equal(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(Equal(0, a - b))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1].reversed
    
    

if __name__ == '__main__':
    prove()
