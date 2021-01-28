from sympy import Symbol, UNION, Exists, Subset

from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains

from sympy.core.numbers import oo

import axiom
from axiom import sets
from sympy.sets.sets import Interval


@apply(given=True)
def apply(imply):
    x, S = axiom.is_Contains(imply)
    function, *limits = axiom.is_UNION(S)    

    for v in S.variables:
        if x._has(v):
            _v = v.generate_free_symbol(imply.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Contains(x, S.function).simplify()
    return Exists(contains, *S.limits)


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(Contains(x, UNION[k:n](A[k])))
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    Eq << Eq[-1].limits_subs(k, i)
    
    Eq << Subset(A[i], Eq[0].rhs, plausible=True)
    Eq << Eq[-1].this.rhs.bisect(i.set)
    
    Eq << Eq[-2].apply(sets.contains.subset.imply.contains, Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)

