from axiom.utility import plausible
from sympy.core.relational import Equality
from sympy import Symbol, ForAll

import axiom
from sympy.core.symbol import Wild
from sympy.core.numbers import oo
from sympy.sets.sets import Interval


@plausible
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


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(integer=True, shape=(oo,))
    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    
    Eq << apply(Equality(f[k], g[k]), Equality(f[n], g[n]), wrt=k)
    
    Eq << Eq[-1].bisect(n.set).split()
    
    Eq << Eq[0].forall((k,))
        
    
if __name__ == '__main__':
    prove(__file__)
