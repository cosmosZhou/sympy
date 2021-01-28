from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(imply=True)
def apply(*given, n=None):    
    f0, sufficient = given
    axiom.is_Equal(f0)
    fk, fn = axiom.is_Sufficient(sufficient)
    
    fk, *limits = axiom.is_ForAll(fk)
    k, start, _n = axiom.limit_is_Interval(limits, integer=True)

    assert fk._subs(k, _n) == fn
    assert fk._subs(k, start) == f0
    diff = _n - n
    if diff:
        assert not diff._has(n)
        fn = fn._subs(n, n - diff)
    assert n.domain.min() == start
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    k = Symbol.k(integer=True)
    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo,), real=True)    
    
    Eq << apply(Equal(f[0], g[0]), Sufficient(ForAll[k:n](Equal(f[k], g[k])), Equal(f[n], g[n])), n=n)
    
    Eq << algebre.sufficient.imply.forall.rewrite.apply(Eq[1], wrt=n)
    
    Eq << Sufficient(ForAll[k:n](Equal(f[k], g[k])), ForAll[k:n](Equal(f[k], g[k])), plausible=True)
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq << algebre.condition.sufficient.imply.condition.induction.apply(Eq[0], Eq[-1], n=n, start=1)

    Eq << Eq[-1].subs(k, n - 1)
    
    Eq << Eq[-1].subs(n, n + 1)

        
if __name__ == '__main__':
    prove(__file__)
