from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(imply=True)
def apply(given, n=None):
    fn, fn1 = axiom.is_Sufficient(given)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, S.Zero)
    assert n.domain.min().is_zero
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    h = Symbol.h(integer=True, shape=(oo,))
    g = LAMBDA[n](Piecewise((f[0], Equal(n, 0)), (h[n], True)))
    
    Eq << apply(Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])), n=n)
    
    g = Symbol.g(definition=LAMBDA[n](Piecewise((f[0], Equal(n, 0)), (h[n], True))))
    Eq.equality = g[0].this.definition.reversed
    
    Eq.sufficient = Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1]), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.rhs.definition
    
    Eq << Eq[-1].this.rhs.rhs.definition

    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.equality, Eq.sufficient, n=n)
    
    Eq << Eq[-1].this.rhs.definition
    
        
if __name__ == '__main__':
    prove(__file__)
