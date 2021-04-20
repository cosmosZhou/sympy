from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebra
import axiom


@apply
def apply(given):
    abs_x, a = axiom.is_Less(given)
    x = axiom.is_Abs(abs_x)
    return Less(x, a), Greater(x, -a)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    
    Eq << apply(abs(x) < a)  
    
    Eq << algebra.lt.gt.imply.lt.abs.apply(Eq[-2], Eq[-1])    
    

if __name__ == '__main__':
    prove()
