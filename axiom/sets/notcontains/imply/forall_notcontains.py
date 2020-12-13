from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import NotContains
from sympy import Symbol
from sympy.core.numbers import oo
from sympy import UNION, ForAll
from sympy.sets.sets import Interval
from axiom import sets


@plausible
def apply(given):
    assert given.is_NotContains    
    
    e, S = given.args
    assert S.is_UNION
    limits = S.limits
    
    return ForAll(NotContains(e, S.function).simplify(), *limits)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotContains(x, UNION[k:n](A[k])))
    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    Eq << Eq[0].this.rhs.bisect(k.set)
    
    Eq << Eq[-1].split()
    
    Eq << Eq[-2].forall((k,))

    
if __name__ == '__main__':
    prove(__file__)

