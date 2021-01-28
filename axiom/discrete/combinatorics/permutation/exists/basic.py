from axiom.utility import prove, apply

from sympy import *
from sympy.sets.conditionset import conditionset
from axiom import sets, algebre


@apply(imply=True)
def apply(n):
    i = Symbol.i(integer=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[p[:n]:P](Exists[i:n](Equality(p[i], n - 1)))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    Eq << Eq[1].subs(Eq[0])
    
    Eq << algebre.imply.forall.limits_assert.apply(Eq[-1].limits)
    
    Eq << Contains(n - 1, Eq[-1].rhs, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << Eq[-1].apply(sets.contains.imply.exists_contains.where.union_comprehension)
    
    Eq << Eq[-1].reversed
    

if __name__ == '__main__':
    prove(__file__)
