from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    et, fx = axiom.is_Necessary(given)
    eqs = axiom.is_And(et)    
    return tuple(Necessary(eq, fx) for eq in eqs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2]), Equal(f[n], g[n])))
    
    Eq << Eq[0].reversed

    Eq << algebra.sufficient.given.sufficient.split.et.apply(Eq[-1])
        
    Eq << Eq[-2].reversed
    
    Eq << Eq[-1].reversed
        
if __name__ == '__main__':
    prove()
