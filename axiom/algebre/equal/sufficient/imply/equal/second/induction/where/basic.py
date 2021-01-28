from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(imply=True)
def apply(*given, n=None, k=None, hypothesis=False):    
    f0, sufficient = given
    axiom.is_Equal(f0)
    fk, fn = axiom.is_Sufficient(sufficient)
    
    assert fk.is_Equal
    
    start, _n = axiom.is_Interval(k.domain, end=None)
    
    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)
    assert n.domain.min() >= start
    
    if hypothesis:
        return fn, fk
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)    
    
    Eq << apply(Equal(f[0], g[0]), Sufficient(Equal(f[k], g[k]), Equal(f[n], g[n])), n=n, k=k, hypothesis=True)
    
    Eq << Eq[1].this.lhs.forall((k,))
    
    Eq << algebre.equal.sufficient.imply.equal.second.induction.where.forall.apply(Eq[0], Eq[-1], n=n)
    
    Eq << Eq[2].subs(n, k)

        
if __name__ == '__main__':
    prove(__file__)
