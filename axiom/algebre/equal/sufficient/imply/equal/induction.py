from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, n=None, start=0):
    start = sympify(start)
    f0, sufficient = given
    axiom.is_Equal(f0)
    fn, fn1 = axiom.is_Sufficient(sufficient)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    assert n.domain.min() >= start
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True, given=False)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(Equal(f[0], g[0]), Sufficient(Equal(f[n], g[n]), Equal(f[n + 1], g[n + 1])), n=n)
    
    h = Symbol.h(LAMBDA[n](f[n] - g[n]))
    
    Eq << h[0].this.definition
    
    Eq.is_zero = Eq[-1].this.rhs.subs(Eq[0])
    
    Eq.sufficient = Sufficient(Equal(h[n], 0), Equal(h[n + 1], 0), plausible=True)

    Eq << Eq.sufficient.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.reversed
    
    Eq << algebre.is_zero.sufficient.imply.is_zero.induction.apply(Eq.is_zero, Eq.sufficient, n=n)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].reversed

        
if __name__ == '__main__':
    prove(__file__)
