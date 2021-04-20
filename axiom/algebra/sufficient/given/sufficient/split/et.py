from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    fx, et = axiom.is_Sufficient(given)
    eqs = axiom.is_And(et)    
    return tuple(Sufficient(fx, eq) for eq in eqs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2])))
    
    Eq << Eq[0].apply(algebra.sufficient.given.ou)
    
    Eq << Eq[1].apply(algebra.sufficient.imply.ou)
    
    Eq << Eq[2].apply(algebra.sufficient.imply.ou)
    
    Eq <<= Eq[-2] & Eq[-1]
        
if __name__ == '__main__':
    prove()
