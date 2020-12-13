from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import Symbol
from sympy import LAMBDA
from axiom.discrete.combinatorics.permutation.index.equality import index_function
from axiom import discrete, algebre
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(given, i=None, j=None):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n - 1
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    
    if i is None:
        i = Symbol.i(domain=[0, n - 1], integer=True, given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n
        
    index = index_function(n)
    
    di = index[i](x[:n])
    dj = index[j](x[:n])
    
    return Equality(KroneckerDelta(di, dj), KroneckerDelta(i, j))


@check
def prove(Eq): 
    
    n = Symbol.n(domain=[2, oo], integer=True)
    
    x = Symbol.x(shape=(n,), integer=True, given=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    i = Symbol.i(domain=[0, n - 1], integer=True, given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), i, j)
    
    Eq << Eq[-1].bisect(Equality(i, j)).split()
    
    Eq <<= ~Eq[-1], ~Eq[-2]
    
    Eq << Eq[-2].apply(algebre.equality.inequality.imply.inequality)

    Eq << Eq[-1].apply(algebre.inequality.inequality.imply.et)

    Eq << discrete.combinatorics.permutation.index.equality.apply(Eq[0], j=j)[1]

    Eq << Eq[-2].this.args[0].rhs.subs(Eq[-1].reversed)
    
    Eq << discrete.combinatorics.permutation.index.equality.apply(Eq[0], j=i)[1]
    
    Eq << Eq[-2].this.args[0].lhs.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(algebre.equality.inequality.imply.inequality)
    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
