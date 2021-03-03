from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given):
    q, p = axiom.is_Necessary(given)
        
    return Equal(Boole(p), Boole(p) * Boole(q))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Necessary(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])))

    Eq << Eq[0].reversed
    
    Eq << algebre.sufficient.imply.equal.bool.apply(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)
