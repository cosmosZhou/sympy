from axiom.utility import prove, apply
from sympy import *
from axiom import sets


@apply(imply=True)
def apply(given):
    assert given.is_NotContains    
    
    e, S = given.args
    assert S.is_UNION
    limits = S.limits
    
    return ForAll(NotContains(e, S.function).simplify(), *limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotContains(x, UNION[k:n](A[k])))
    
    k = Symbol.k(domain=Interval(0, n - 1, integer=True))
    Eq << Eq[0].this.rhs.bisect(k.set)
    
    Eq << sets.notcontains.imply.et.where.union.apply(Eq[-1], simplify=None).split()
    
    Eq << Eq[-2].forall((k,))

    
if __name__ == '__main__':
    prove(__file__)

