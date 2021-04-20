from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    p, q = axiom.is_Necessary(given)        
    return p | q.invert()


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Necessary(x > y, f(x) > g(y)))
    
    Eq << Eq[0].reversed
    
    Eq << Eq[-1].apply(algebra.sufficient.imply.ou)
    
        
if __name__ == '__main__':
    prove()
