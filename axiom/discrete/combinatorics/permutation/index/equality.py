from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import Symbol
from sympy.functions.special.tensor_functions import KroneckerDelta
from axiom.sets.is_nonemptyset.imply import greater_than
from axiom import sets
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.expr_with_limits import LAMBDA, ForAll
from sympy.sets.contains import Contains, Subset
from sympy.core.function import Function
from sympy.logic.boolalg import Or

def index_function(n):
    index = Function.index(nargs=(n,), shape=(), integer=True)
    k = Symbol.k(integer=True)
    
    def eval(x, *indices):
        (j,), *_ = indices
        return LAMBDA[k:n](KroneckerDelta(x[k], j)) @ LAMBDA[k:n](k)

    index.eval = eval
    return index
    
    k = Symbol.k(integer=True)
    index = Function.index(nargs=(n,), 
                           shape=(), 
                           integer=True, 
                           eval=lambda x, *indices: LAMBDA[k:n](KroneckerDelta(x[k],
                                                                               indices[0][0])) @ LAMBDA[k:n](k))
    return index


@plausible
def apply(given, j=None):
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
    
    assert j >= 0 and j < n
        
    index = index = index_function(n)
    index_j = index[j](x[:n], evaluate=False)
#     index_j = index[j](x[:n])
    return Contains(index_j, Interval(0, n - 1, integer=True), given=given), Equality(x[index_j], j, given=given),


@check
def prove(Eq): 
    
    n = Symbol.n(domain=[2, oo], integer=True)
    
    x = Symbol.x(shape=(oo,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), j)    
    
    Eq << Eq[1].lhs.this.definition
    
    Eq <<= Eq[-3].subs(Eq[-1]), Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].lhs.indices[0].this.expand()    
    
    Eq << Eq[-1].rhs.function.args[1].this.astype(Piecewise)
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].rhs.subs(1, 0).this.bisect({0})
    
    assert Eq[-1].lhs.limits[0][1].args[-1][-1].step.is_zero == False
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    assert Eq[-1].rhs.limits[0][1].args[-1][-1].step.is_zero == False
    
    sj = Symbol.s_j(definition=Eq[-1].rhs.limits[0][1])
    
    Eq.sj_definition = sj.equality_defined()
    assert Eq.sj_definition.rhs.limits[0][-1].step.is_zero == False
    
    Eq.crossproduct = Eq[-1].subs(Eq.sj_definition.reversed)    
    
    Eq.sj_definition_reversed = Eq.sj_definition.this.rhs.limits[0][1].reversed
    assert Eq.sj_definition_reversed.args[-1].args[-1][-1].step.is_zero == False
    Eq.sj_definition_reversed = Eq.sj_definition_reversed.reversed
    
    assert Eq.sj_definition_reversed.lhs.args[-1][-1].step.is_zero == False
    
    Eq << Eq[0].intersect({j})
    
    Eq << Piecewise((x[k].set, Equality(x[k], j)), (x[k].emptySet, True)).this.simplify()
    
    Eq << Eq[-1].reversed.union_comprehension((k, 0, n - 1))
    
    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed
    
    Eq << Eq.distribute.this.lhs.function.subs(Eq.distribute.lhs.limits[0][1].args[1][1])
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].subs(Eq.sj_definition_reversed)
    
    Eq.sj_greater_than_1 = greater_than.apply(Eq[-1])
    
    Eq.distribute = Eq.distribute.subs(Eq.sj_definition_reversed)
    
    Eq << sets.imply.ou.inequality.apply(Eq.sj_greater_than_1.lhs.arg)
    
    Eq.sj_less_than_1, Eq.inequality_ab = Eq[-1].split()
    
    (a, *_), (b, *_) = Eq.inequality_ab.limits
    
    Eq << sets.equality.imply.forall_equality.nonoverlapping.apply(Eq[0].abs(), excludes=Eq.inequality_ab.variables_set)
    
    Eq << Eq[-1].subs(k, a)
    
    Eq << Eq[-1].subs(Eq[-1].variable, b)
    
    Eq << (Eq.inequality_ab & Eq[-1])
    
    Eq.distribute_ab = Eq[-1].this.function.distribute()

    Eq.j_equality, _ = sj.assertion().split()
    
    Eq.i_domain = ForAll[a:sj](Contains(a, Interval(0, n - 1, integer=True)), plausible=True)
    Eq << Eq.i_domain.simplify()
    
    Eq.sj_element_contains = ForAll[b:sj](Contains(b, Interval(0, n - 1, integer=True)), plausible=True)
    Eq << Eq.sj_element_contains.simplify()
    
    Eq << Eq.i_domain.apply(sets.contains.imply.equality.union)
    
    Eq << Eq.distribute_ab.subs(Eq[-1])
    
    Eq << (Eq[-1] & Eq.sj_element_contains)
    
    Eq << Eq.j_equality.limits_subs(k, a).reversed
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq.j_equality.limits_subs(k, b).reversed
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq.sj_less_than_1.subs(Eq.sj_greater_than_1)
    
    Eq << sets.equality.imply.contains.apply(Eq[-1], var=k)
    
    Eq.index_domain = Eq[-1].subs(Eq.crossproduct.reversed)
    
    Eq << Eq.j_equality.subs(k, Eq.index_domain.lhs).split()
    
    Eq <<= Eq[-2] & Eq.index_domain
    
    Eq << Eq[-1].reversed

    Eq << Subset(sj, Eq[1].rhs, plausible=True)
    
    Eq <<= Eq[-1] & Eq.index_domain

    
#     Eq << Eq.index_domain.subs(Eq.sj_definition)
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
