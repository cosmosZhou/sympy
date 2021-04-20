from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


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
    
    Eq << apply(LessEqual(f[0], g[0]), Sufficient(LessEqual(f[n], g[n]), LessEqual(f[n + 1], g[n + 1])), n=n)
    
    h = Symbol.h(LAMBDA[n](Bool(f[n] <= g[n])))
    
    Eq << h[0].this.definition
    
    Eq << algebra.cond.imply.eq.bool.apply(Eq[0])
    
    Eq.initial = algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])
    
    Eq.sufficient = Sufficient(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << algebra.eq.sufficient.imply.eq.induction.apply(Eq.initial, Eq.sufficient, n=n)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.definition

        
if __name__ == '__main__': 
    prove()
    
from . import rhs
from . import lhs
