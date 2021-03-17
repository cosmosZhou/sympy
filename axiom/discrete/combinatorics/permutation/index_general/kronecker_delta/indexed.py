from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply
def apply(given, i=None, j=None):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    if i is None:
        i = Symbol.i(domain=Interval(0, n - 1, integer=True), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n
        
    return Equality(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove
def prove(Eq): 
    
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    x = Symbol.x(shape=(n,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), i, j)

    Eq << Eq[-1].bisect(Equality(i, j))
    
    Eq << algebre.et.given.cond.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebre.eq.ne.imply.ne.subs)
    
    Eq << Eq[-1].apply(algebre.ne.cond.imply.et)

    Eq << Eq[0].apply(algebre.eq.imply.eq.abs)
    
    Eq << sets.eq.imply.forall_is_emptyset.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].rhs.indices[0], j)

    Eq << Eq[-1].subs(Eq[-1].variable, i)

    Eq << ~Eq[-1]
    
    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
