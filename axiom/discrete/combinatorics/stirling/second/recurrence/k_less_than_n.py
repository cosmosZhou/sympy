from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.contains import Contains
from axiom import discrete, algebre
from sympy.sets.conditionset import conditionset
from sympy.sets.sets import Interval


@apply
def apply(n, k):
    assert k < n
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(domain=Interval(1, n - 1, integer=True))    
    Eq << apply(n, k)

    Eq.stirling2 = Eq[0].lhs.this.definition
    Eq.stirling0 = Eq[0].rhs.args[1].this.definition
    Eq.stirling1 = Eq[0].rhs.args[0].args[1].this.definition

    s2 = Symbol.s2(definition=Eq.stirling2.rhs.arg)
    Eq << s2.this.definition
    
    Eq.stirling2 = Eq.stirling2.subs(Eq[-1].reversed)

    s0 = Symbol.s0(definition=Eq.stirling0.rhs.arg)
    Eq << s0.this.definition
    
    Eq.stirling0 = Eq.stirling0.subs(Eq[-1].reversed)

    s1 = Symbol.s1(definition=Eq.stirling1.rhs.arg)
    Eq << s1.this.definition
     
    Eq.stirling1 = Eq.stirling1.subs(Eq[-1].reversed)
    e = Symbol.e(etype=dtype.integer.set)

    Eq << s2.this.bisect(conditionset(e, Contains({n}, e), s2))

    Eq.s2_abs = Eq[-1].apply(algebre.equal.imply.equal.abs)    

    Eq.s2_abs_plausible = Eq[0].subs(Eq.stirling2, Eq.stirling0, Eq.stirling1)

    Eq << discrete.combinatorics.stirling.second.mapping.s2_A.apply(n, k, s2)
    
    A = Eq[-1].rhs.function.base

    Eq << discrete.combinatorics.stirling.second.mapping.s2_B.apply(n, k, s2)
    B = Eq[-1].rhs

    Eq.s2_abs = Eq.s2_abs.subs(Eq[-1], Eq[-2])

    Eq << discrete.combinatorics.stirling.second.mapping.s0_B.apply(n, k, s0, B)

    Eq << Eq.s2_abs.subs(Eq[-1].reversed)

    Eq.A_union_abs = Eq.s2_abs_plausible.subs(Eq[-1])

    Eq << discrete.combinatorics.stirling.second.nonoverlapping.apply(n, k, A)

    Eq << Eq.A_union_abs.subs(Eq[-1])
    
    Eq << discrete.combinatorics.stirling.second.mapping.s1_Aj.apply(n, k, s1, A).reversed

    Eq << Eq[-1].apply(algebre.equal.imply.equal.sum, *Eq[-2].lhs.limits)    


if __name__ == '__main__':
#     python run.py axiom.discrete.matrix.elementary.shift.left axiom.discrete.combinatorics.stirling.second.mapping.s2_B axiom.keras.softmax.crossentropy axiom.discrete.combinatorics.permutation.mapping.Qu2v_exist axiom.discrete.combinatorics.stirling.second.recurrence axiom.keras.adam axiom.discrete.matrix.elementary.multiply.right axiom.statistics.bayes.equal.equal.given_deletion.single_condition_w axiom.discrete.combinatorics.permutation.factorial.definition axiom.sets.equal.imply.equal.union axiom.discrete.combinatorics.binomial.Pascal axiom.sets.equal.imply.exists_equal.general axiom.discrete.combinatorics.permutation.push_back axiom.discrete.matrix.inequality.equality axiom.statistics.bayes.theorem axiom.discrete.kronecker_delta.equality1 axiom.sets.contains.contains.imply.subset axiom.sets.exists.imply.exists.limits_swap axiom.sets.exists.imply.exists.enlargement axiom.sets.subset.imply.less_than axiom.algebre.strict_greater_than.imply.unequal axiom.statistics.total_probability_theorem axiom.sets.contains.subset.imply.contains
# python run.py axiom.discrete.matrix.elementary.swap.transpose axiom.statistics.chiSquared.definition axiom.discrete.combinatorics.stirling.second.mapping.s2_B axiom.discrete.matrix.vandermonde.matmul_equal axiom.discrete.combinatorics.permutation.mapping.Qu2v_exist axiom.discrete.combinatorics.stirling.second.recurrence axiom.statistics.guassion.std axiom.discrete.combinatorics.permutation.adjacent.swap2.general axiom.discrete.combinatorics.permutation.pop_back axiom.calculus.integral.mean_value_theorem axiom.statistics.bayes.equal.equal.conditional_joint_probability.nonzero axiom.sets.contains.imply.equal.union axiom.statistics.bayes.is_nonzero.strict_greater_than axiom.sets.equal.imply.exists_equal.general axiom.discrete.combinatorics.binomial.expand axiom.sets.forall_contains.forall_contains.forall_equal.imply.equal axiom.sets.imply.less_than.intersection axiom.discrete.combinatorics.permutation.index.exists axiom.sets.subset.imply.forall axiom.discrete.matrix.inequality.inequality axiom.sets.exists.imply.exists.enlargement axiom.algebre.strict_greater_than.imply.unequal axiom.sets.is_emptyset.imply.equal.notcontains axiom.sets.contains.imply.equal.intersection axiom.discrete.fermat.last_theorem axiom.sets.is_positive.imply.exists_contains
# python run.py axiom.statistics.guassion.sum axiom.discrete.matrix.elementary.swap.transpose axiom.discrete.combinatorics.stirling.second.nonoverlapping axiom.discrete.combinatorics.stirling.second.mapping.s2_B axiom.discrete.matrix.elementary.swap.multiply.left axiom.discrete.combinatorics.permutation.index.equal axiom.discrete.matrix.determinant.abc axiom.discrete.combinatorics.stirling.second.recurrence axiom.discrete.combinatorics.permutation.adjacent.swap2.equality axiom.discrete.difference.factorial axiom.calculus.integral.mean_value_theorem axiom.statistics.bayes.equal.equal.given_addition.condition_probability axiom.discrete.matrix.elementary.swap.concatenate_product axiom.discrete.combinatorics.permutation.factorial.definition axiom.discrete.matrix.elementary.swap.invariant.permutation axiom.discrete.combinatorics.permutation.index.exists axiom.sets.is_emptyset.imply.equal.addition_principle axiom.statistics.bayes.is_nonzero.is_nonzero.conditioned axiom.sets.contains.forall.imply.condition axiom.sets.greater_than.imply.exists_unequal axiom.discrete.combinatorics.permutation.factorial.expand axiom.algebre.strict_greater_than.imply.unequal axiom.sets.is_emptyset.imply.equal.intersect axiom.sets.forall.imply.forall_contains axiom.sets.ou.imply.forall axiom.sets.is_nonemptyset.subset.imply.unequal axiom.sets.is_nonemptyset.imply.exists_contains.overlapping axiom.sets.subset.imply.subset axiom.sets.is_emptyset.subset.imply.equal axiom.sets.is_emptyset.imply.subset.complement axiom.algebre.is_nonzero.imply.equal.kronecker_delta axiom.discrete.fermat.last_theorem axiom.sets.is_nonemptyset.imply.strict_greater_than axiom.sets.equal.imply.supset
    prove(__file__)

