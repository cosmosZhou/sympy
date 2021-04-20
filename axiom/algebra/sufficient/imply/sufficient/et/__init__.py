from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply(simplify=False)
def apply(given, index=None):
    fx, fy = axiom.is_Sufficient(given)
    if index is None:
        cond = fx    
    else:
        eqs = axiom.is_And(fx)
        cond = eqs[index]
        if isinstance(index, slice):
            cond = And(*cond)
        
    return Sufficient(fx, cond & fy)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    A = Symbol.A(etype=dtype.integer)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]) & Contains(n, A), Equal(f[n + 1], g[n + 1])), index=0)
    
    Eq << Sufficient(Equal(f[n], g[n]) & Contains(n, A), Equal(f[n], g[n]), plausible=True)
    
    Eq << algebra.sufficient.sufficient.imply.sufficient.et.apply(Eq[0], Eq[-1], simplify=False)
    
    
        
if __name__ == '__main__':
    prove()
from . import both_sided
