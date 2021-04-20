from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    q, p = axiom.is_Necessary(given)
        
    return Equal(Bool(p), Bool(p) * Bool(q))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Eq[0].reversed
    
    Eq << algebra.sufficient.imply.eq.bool.apply(Eq[-1])

    
if __name__ == '__main__':
    prove()
