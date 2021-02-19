from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, n=None, start=0):
    start = sympify(start)
    f0, sufficient = given
    fn, fn1 = axiom.is_Sufficient(sufficient)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    a = n.domain.min()
    if a == start:        
        return fn
    if a < start:
        diff = start - a
        if diff.is_Number:
            for i in range(diff):
                if fn._subs(n, a + i):
                    continue
                return
            return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    Eq << apply(LessThan(f[0], g[0]), Sufficient(LessThan(f[n], g[n]), LessThan(f[n + 1], g[n + 1])), n=n)
    
    h = Symbol.h(definition=LAMBDA[n](Boole(f[n] <= g[n])))
    
    Eq << h[0].this.definition
    
    Eq << algebre.less_than.imply.equal.bool.apply(Eq[0])
    
    Eq.equality = Eq[-1] + Eq[-2]
    
    Eq.sufficient = Sufficient(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.astype(Piecewise)
    
    Eq << algebre.equal.sufficient.imply.equal.induction.apply(Eq.equality, Eq.sufficient, n=n)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)

        
if __name__ == '__main__':
    prove(__file__)
