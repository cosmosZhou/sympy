from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    fx, fy = axiom.is_Sufficient(given)    
    return Equivalent(fx, fx & fy)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))
    
    Eq.sufficient, Eq.necessary = algebra.equivalent.given.cond.apply(Eq[1])
    
    Eq << algebra.sufficient.imply.sufficient.et.apply(Eq[0])
    
    
        
if __name__ == '__main__':
    prove()

