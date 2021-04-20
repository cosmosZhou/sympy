from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    p, q = axiom.is_Sufficient(given)        
    return p.invert() | q


@prove
def prove(Eq):
    x = Symbol.x(integer=True)    
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    
    Eq << apply(Sufficient(x > y, f(x) > g(y)))
    
    Eq << Eq[0].this.apply(algebra.sufficient.to.ou)
    
        
if __name__ == '__main__':
    prove()
