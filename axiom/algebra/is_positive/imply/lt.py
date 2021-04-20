from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import algebra


@apply
def apply(given):
    xy = axiom.is_positive(given)
    x, y = axiom.is_Substract(xy)
    
    return Less(y, x)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    Eq << apply(Less(0, a - b))
    
    Eq << Eq[0] + b
    
    Eq << Eq[-1]
    
    

if __name__ == '__main__':
    prove()
