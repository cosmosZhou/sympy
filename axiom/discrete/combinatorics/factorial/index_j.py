from sympy.core.relational import Equality
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval, EmptySet
from sympy.core.numbers import oo

from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.concrete import expr_with_limits
from axiom.discrete.sets.emptyset import greater_than_one
from axiom.discrete.sets import union_comprehension
from axiom.discrete import sets
from sympy.core.symbol import Symbol
from sympy.functions.elementary.piecewise import Piecewise


@plausible
def apply(given):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n - 1
    x = expr_with_limits.Ref(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    return Equality(x[Ref[k:n](KroneckerDelta(x[k], j)) @ Ref[k:n](k)], j, given=given)


@check
def prove(Eq): 
    
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    
    x = IndexedBase('x', (n,), integer=True)    
    
    k = Symbol('k', integer=True)    
    given = Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True))    

    Eq << apply(given)    
    
    Eq << identity(Eq[-1].lhs.indices[0]).expand()    
    
    Eq << identity(Eq[-1].rhs.function.args[1]).definition
    
    Eq << Eq[-2].this.rhs.subs(Eq[-1])
    
    Eq << identity(Eq[-1].rhs.subs(1, 0)).bisect(domain={0})
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    sj = Symbol('s_j', definition=Eq[-1].rhs.limits[0][1])
    
    Eq.sj_definition = Equality.by_definition_of(sj)
    Eq.crossproduct = Eq[-1].subs(Eq.sj_definition.reversed)
    
    Eq.sj_definition_reversed = Eq.sj_definition.this.rhs.limits[0][1].reversed
    
    Eq.sj_definition_reversed = Eq.sj_definition_reversed.reversed
    
    j = Eq[1].rhs
    Eq << Eq[0].intersect({j})
    
    Eq << identity(Piecewise((x[k].set, Equality(x[k], j)), (EmptySet(), True))).simplify()
    
    Eq << Eq[-1].reversed.union_comprehension((k, 0, n - 1))
    
    Eq.distribute = Eq[-1].subs(Eq[-3]).reversed
    
    Eq << Eq.distribute.this.lhs.function.subs(Eq.distribute.lhs.limits[0][1].args[1][1])
    
    Eq << Eq[-1].subs(Eq.sj_definition_reversed)
    
    Eq.sj_greater_than_1 = greater_than_one.apply(Eq[-1])
    
    Eq.distribute = Eq.distribute.subs(Eq.sj_definition_reversed)
    
    Eq << Eq.sj_greater_than_1.lhs.assertion()
    
    Eq.inequality_ab, Eq.sj_less_than_1 = Eq[-1].split()
    
    (a, *_), (b, *_) = Eq.inequality_ab.limits
    
    Eq << union_comprehension.nonoverlapping.apply(Eq[0].abs())
    
    Eq << Eq[-1].subs(k, a)
    
    Eq << Eq[-1].subs(Eq[-1].variable, b)
    
    Eq << (Eq.inequality_ab & Eq[-1])
    
    Eq.distribute_ab = Eq[-1].this.function.distribute()

    Eq.j_equality, Eq.k_domain = sj.assertion().split()
    
    Eq << Eq.k_domain.limits_subs(k, a).apply(sets.contains.union)
    
    Eq << Eq.distribute_ab.subs(Eq[-1])
    
    Eq << (Eq[-1] & Eq.k_domain.limits_subs(k, b))
    
    Eq << Eq.j_equality.limits_subs(k, a).reversed
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq.j_equality.limits_subs(k, b).reversed
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << Eq.sj_less_than_1.subs(Eq.sj_greater_than_1)
    
    Eq.a_relation = sets.equality.exists.apply(Eq[-1]).reversed
    
    Eq.crossproduct = Eq.crossproduct.subs(Eq.a_relation).reversed
    
    Eq << Eq.j_equality.subs(k, a)
    
    Eq << Eq.a_relation.intersect(Eq.a_relation.rhs).apply(sets.equality.contains)
    
    Eq << (Eq[-1] & Eq[-2]).reversed
    
    Eq << Eq[-1].subs(Eq.crossproduct)    

    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
