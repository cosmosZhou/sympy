from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra, sets


@apply
def apply(*given, n=None, start=0):
    start = sympify(start)
    f0, sufficient = given
    axiom.is_Contains(f0)
    
    fn, fn1 = axiom.is_Sufficient(sufficient)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    assert n.domain.min() == start
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(etype=dtype.integer, shape=(oo,))
    
    Eq << apply(Contains(f[0], g[0]), Sufficient(Contains(f[n], g[n]), Contains(f[n + 1], g[n + 1])), n=n)
    
    h = Symbol.h(LAMBDA[n](Bool(Contains(f[n], g[n]))))
    
    Eq << h[0].this.definition
    
    Eq << sets.contains.imply.eq.bool.contains.apply(Eq[0])
    
    Eq << Eq[-1] + Eq[-2]
    
    Eq.equality = Eq[-1].this.apply(algebra.eq.simplify.terms.common)
    
    Eq.sufficient = Sufficient(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)
    
    Eq << Eq.sufficient.this.lhs.lhs.definition
    
    Eq << Eq[-1].this.lhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << Eq[-1].this.rhs.lhs.definition
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq.equality, Eq.sufficient, n=n)

    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.definition

        
if __name__ == '__main__':
    prove()
