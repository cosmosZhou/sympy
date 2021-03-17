from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, wrt=None): 
    eq_k, eq_n = given
    axiom.is_Equal(eq_k)
    axiom.is_Equal(eq_n)
    
    pattern = eq_k._subs(wrt, Wild('k', **wrt.type.dict))
    res = eq_n.match(pattern)
    n, *_ = res.values()
    domain = wrt.domain
    assert n not in domain
    domain |= n.set
    
    k = wrt.unbounded
    
    return ForAll[k:domain](eq_k._subs(wrt, k))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    
    Eq << apply(Equality(f[k], g[k]), Equality(f[n], g[n]), wrt=k)
    
    Eq << Eq[-1].bisect(n.set)
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    Eq << Eq[0].forall((k,))
        
    
if __name__ == '__main__':
    prove(__file__)
