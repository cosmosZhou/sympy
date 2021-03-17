from sympy import *
from axiom.utility import prove, apply
from axiom import sets, discrete, algebre
from axiom.discrete.combinatorics.permutation.index.eq import index_function


@apply
def apply(given, j=None):
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
    
    assert j >= 0 and j < n
        
    index = index_function(n)
 
    return Equality(index[x[j]](x[:n]), j)


@prove
def prove(Eq): 
    
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    x = Symbol.x(shape=(oo,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), j)
    
    t = Symbol.t(domain=Interval(0, n - 1, integer=True))
    
    Eq << discrete.combinatorics.permutation.index.eq.apply(Eq[0], j=t)
    
    Eq.ou = Eq[-1].subs(t, x[j])
    
    Eq.equality = Eq.ou.args[0].copy(plausible=True)
    
    Eq.xj_notcontains = Eq.ou.args[1].copy(plausible=True)
    
    Eq << sets.eq.imply.subset.apply(Eq[0])
    
    Eq << sets.subset.imply.forall_subset.having.union_comprehension.apply(Eq[-1])
    
    Eq <<= Eq[-1].subs(Eq[-1].variable, j) & Eq.xj_notcontains
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    Eq << discrete.combinatorics.permutation.index.kronecker_delta.indexed.apply(Eq[0], i, j)
    
    Eq.ou1 = Eq[-1].subs(i, Eq[1].lhs)
    
    Eq << Eq.ou1.args[1].copy(plausible=True)
    
    Eq.ou2 = Eq[2].subs(t, x[j])
    
    Eq <<= Eq.ou2.args[0].copy(plausible=True), Eq.ou2.args[1].copy(plausible=True)
    
    Eq << algebre.et.imply.cond.apply(Eq.ou & ~Eq.xj_notcontains, index=0)
    
    Eq << algebre.et.imply.cond.apply(Eq.ou1 & Eq[-1], index=1)
    
    Eq << algebre.et.imply.cond.apply(Eq.ou2 & ~Eq.xj_notcontains, index=0)
    
    Eq << Eq[-2].subs(Eq.equality)
    
    Eq << Eq[-1].reversed

    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html


