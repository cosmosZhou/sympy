from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, wrt=None):
    cond, q = axiom.is_Sufficient(given)
    if wrt is None:
        wrt = cond.wrt 
    return ForAll[wrt:cond](q)


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Sufficient(x > y, f(x) > g(y)))
    
    Eq << algebra.sufficient.imply.ou.apply(Eq[0])
    
    Eq << Eq[-1].apply(algebra.ou.imply.forall, pivot=1)
    
        
if __name__ == '__main__':
    prove()
