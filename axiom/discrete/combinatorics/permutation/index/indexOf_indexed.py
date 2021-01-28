from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.sets.sets import Interval
from sympy import *
from axiom import sets, discrete
from axiom.discrete.combinatorics.permutation.index.equal import index_function

@apply(imply=True)
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
    
    Eq << discrete.combinatorics.permutation.index.equal.apply(Eq[0], j=t)
    
    Eq.equality, Eq.xj_notcontains = Eq[-1].subs(t, x[j]).split()
    
    Eq << sets.equal.imply.subset.apply(Eq[0])
    
    Eq << sets.subset.imply.forall_subset.where.union_comprehension.apply(Eq[-1])
    
    Eq <<= Eq[-1].subs(Eq[-1].variable, j) & Eq.xj_notcontains
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    Eq << discrete.combinatorics.permutation.index.kronecker_delta.indexed.apply(Eq[0], i, j)
    
    Eq << Eq[-1].subs(i, Eq[1].lhs).split()
    
    Eq << Eq[2].subs(t, x[j]).split()
    
    Eq <<= Eq[-1] & Eq[-3]
    
    Eq << Eq[-2].subs(Eq.equality)
    
    Eq << Eq[-1].reversed
    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html


