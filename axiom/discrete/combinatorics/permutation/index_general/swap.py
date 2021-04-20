from sympy import *
from axiom.utility import prove, apply
from axiom.discrete.combinatorics.permutation.index.eq import index_function
from sympy.matrices.expressions.matexpr import Swap
from axiom import discrete, sets, algebra


@apply
def apply(given, i=None, j=None, w=None):
    assert given.is_Equal
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
        
    index = index_function(n)
    if w is None:
        _i = Symbol.i(integer=True)
        _j = Symbol.j(integer=True)
        w = Symbol.w(LAMBDA[_j, _i](Swap(n, _i, _j)))
    
    return Equal(index[i](w[index[i](x[:n]), index[j](x[:n])] @ x[:n]), index[j](x[:n]))


@prove
def prove(Eq): 
    
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    x = Symbol.x(shape=(n,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    i = Symbol.i(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equal(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), i, j)
        
    _, di, dj = Eq[2].lhs.arg.args[0].args
    dj = Symbol("d_j", dj)
    di = Symbol("d_i", di)
    
    Eq.dj_definition = dj.this.definition
    Eq.di_definition = di.this.definition
    
    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)
    
    _i, _j = Eq[0].lhs.indices
    Eq << Eq[0].subs(_i, di).subs(_j, dj)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.definition = Eq[-1].this.lhs.definition
    
    Eq.expand = Eq.definition.lhs.args[0].function.args[1].this.expand()
    
    Eq << discrete.combinatorics.permutation.index.eq.apply(Eq[1], j=j)
        
    Eq.dj_domain, Eq.x_dj_eqaulity = Eq[-2].subs(Eq.dj_definition.reversed), Eq[-1].subs(Eq.dj_definition.reversed)

    Eq.expand = Eq.expand.subs(Eq.x_dj_eqaulity)
    
    Eq << discrete.combinatorics.permutation.index.eq.apply(Eq[1], j=i)
    Eq.di_domain, Eq.x_di_eqaulity = Eq[-2].subs(Eq.di_definition.reversed), Eq[-1].subs(Eq.di_definition.reversed)
    
    Eq << sets.contains.contains.imply.subset.apply(Eq.dj_domain, Eq.di_domain, simplify=False)
    
    Eq << Eq.expand.subs(Eq.x_di_eqaulity)
    
    Eq.union_equality, Eq.piecewise_equality = sets.subset.imply.eq.union.apply(Eq[-2]), Eq.definition.subs(Eq[-1])
    
    Eq.piecewise_equality = Eq.piecewise_equality.this.lhs.expand()
    
    Eq << Eq.piecewise_equality.lhs.args[-1].this.bisect({di, dj})
    
    Eq << Eq[-1].subs(Eq.x_dj_eqaulity).subs(Eq.x_di_eqaulity)
    
    Eq << Eq[-1].this.rhs.subs(Eq.union_equality)
    
    Eq << Eq.di_definition.this.rhs.definition.this.rhs.expand()
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.piecewise_equality = Eq.piecewise_equality.subs(Eq[-1])

    Eq.dj_eq = sets.contains.imply.eq.piecewise.expr_swap.apply(Eq.dj_domain, Eq.piecewise_equality.lhs.args[2])
    
    Eq << sets.contains.imply.eq.piecewise.expr_swap.apply(Eq.di_domain, Eq.piecewise_equality.lhs.args[-1])

    Eq << sets.contains.imply.eq.intersection.apply(Eq.dj_domain)
    
    Eq << algebra.eq.eq.imply.eq.subs.apply(Eq[-1], Eq[-2])
    
    Eq << Eq[-1].this.rhs.find(Contains).simplify()
    
    Eq << Eq.dj_eq + Eq[-1]
    
    Eq << Eq.piecewise_equality.subs(Eq[-1]) 

    Eq << discrete.combinatorics.permutation.index.kronecker_delta.indexOf.apply(Eq[1], i, j)
    
    Eq << Eq[-1].subs(Eq.di_definition.reversed).subs(Eq.dj_definition.reversed)
    
    Eq << Eq[-3].subs(Eq[-1].reversed)
    
        
if __name__ == '__main__':
    prove()
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
