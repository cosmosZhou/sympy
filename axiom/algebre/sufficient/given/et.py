from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(given):
    fx, et = axiom.is_Sufficient(given)
    eqs = axiom.is_And(et)    
    return And(*(Sufficient(fx, eq) for eq in eqs))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]) & Equal(f[n + 2], g[n + 2])))
    
    Eq << Eq[0].astype(Or)
    
    Eq << Eq[-1].astype(And)
    
    Eq << Eq[1].this.args[0].astype(Or)
    
    Eq << Eq[-1].this.args[1].astype(Or)
    
    
        
if __name__ == '__main__':
    prove(__file__)
