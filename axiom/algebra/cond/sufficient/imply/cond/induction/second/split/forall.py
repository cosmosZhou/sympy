from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given, n=None): 
    f0, sufficient = given
#     axiom.is_Equal(f0)
    fk, fn = axiom.is_Sufficient(sufficient)
    
    fk, *limits = axiom.is_ForAll(fk)
    k, start, _n = axiom.limit_is_Interval(limits, integer=True)

    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)
        
    n_domain = fn.domain_defined(n)
    assert n_domain.min() >= start
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    k = Symbol.k(integer=True)
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)    
    
    Eq << apply(f[0] > g[0], Sufficient(ForAll[k:n](f[k] > g[k]), f[n] > g[n]), n=n)
    
    Eq << Eq[1].this.apply(algebra.sufficient.to.forall, wrt=n)
    
    Eq << Sufficient(ForAll[k:n](f[k] > g[k]), ForAll[k:n](f[k] > g[k]), plausible=True)
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq << Eq[-1].this.rhs.apply(algebra.cond.forall.imply.forall.absorb.back)
    
    Eq << algebra.cond.sufficient.imply.cond.induction.apply(Eq[0], Eq[-1], n=n, start=1)

    Eq << algebra.forall.imply.ou.subs.apply(Eq[-1], k, n - 1)
    
    Eq << Eq[-1].subs(n, n + 1)

        
if __name__ == '__main__':
    prove()
