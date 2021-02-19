from axiom.utility import prove, apply
from sympy import *
from axiom import sets, discrete, algebre

def index_function(n):    
    k = Symbol.k(integer=True)
    
    def index(x, *indices):
        (j,), *_ = indices
        return LAMBDA[k:n](KroneckerDelta(x[k], j)) @ LAMBDA[k:n](k)

    f = Function.index(nargs=(n,), shape=(), integer=True)
    f.eval = index
    return f

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
    index_j = index[j](x[:n], evaluate=False)
#     index_j = index[j](x[:n])
    return Contains(index_j, Interval(0, n - 1, integer=True)), Equality(x[index_j], j)


@prove
def prove(Eq): 
    
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    x = Symbol.x(shape=(oo,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), j)    
    
    a = Symbol.a(definition=LAMBDA[k:n](k))
    Eq.aj_definition = a.this.definition[j]
    
    Eq << a.set_comprehension().this.function.arg.base.definition
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.abs)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[0], Eq[-2])
    
    Eq << discrete.combinatorics.permutation.index_general.equal.apply(Eq[-2], Eq[-1])
    
    Eq <<= Eq[-2].this.lhs.definition, Eq[-1].this.lhs.indices[0].definition
    
    Eq <<= Eq[-2].subs(Eq.aj_definition), Eq[-1].subs(Eq.aj_definition)
    
    Eq << Eq[1].this.lhs.definition
    
    Eq << Eq[2].this.lhs.indices[0].definition
    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
