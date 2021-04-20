from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(*given, n=None, k=None, hypothesis=False):    
    f0, sufficient = given
    
    fk, fn = axiom.is_Sufficient(sufficient)
    
    start, _n = axiom.is_Interval(k.domain)
    
    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)
        
    domain = fn.domain_defined(n)
    assert domain >= start
    
    if hypothesis:
        return fn, fk
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)    
    
    Eq << apply(f[0] > g[0], Sufficient(f[k] > g[k], f[n] > g[n]), n=n, k=k, hypothesis=True)
    
    Eq << Eq[1].this.lhs.forall((k,))
    
    Eq << algebra.cond.sufficient.imply.cond.induction.second.split.forall.apply(Eq[0], Eq[-1], n=n)
    
    Eq << Eq[2].subs(n, k)

        
if __name__ == '__main__':
    prove()

from . import split