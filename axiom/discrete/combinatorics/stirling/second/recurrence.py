from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality, Unequality
from sympy.utility import plausible, Sum, Ref, Union, identity

from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import image_set, Interval
from sympy.sets.contains import Subset, Supset, Contains, NotContains
from sympy.functions.elementary.piecewise import Piecewise
from sympy.tensor.indexed import IndexedBase
from axiom import discrete
from sympy.sets.conditionset import conditionset
from sympy.concrete.expr_with_limits import UnionComprehension, Forall
import axiom
from sympy.core.numbers import oo


@plausible
def apply(n, k):
    return Equality(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


from sympy.utility import check


@check
def prove(Eq):
    k = Symbol('k', integer=True, nonnegative=True)

    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(n, k)

    Eq.stirling2 = identity(Eq[0].lhs).definition
    Eq.stirling0 = identity(Eq[0].rhs.args[0]).definition
    Eq.stirling1 = identity(Eq[0].rhs.args[1].args[1]).definition

    s2 = Symbol('s2', definition=Eq.stirling2.rhs.arg)
    Eq << identity(s2).definition
    s2_quote = Symbol("s'_2", definition=Eq.stirling2.rhs.arg.limits[0][1])
    Eq.stirling2 = Eq.stirling2.subs(Eq[-1].reversed)
    Eq << identity(s2_quote).definition

    Eq.s2_definition = Eq[-2].subs(Eq[-1].reversed)

    s0 = Symbol('s0', definition=Eq.stirling0.rhs.arg)
    Eq << identity(s0).definition
    s0_quote = Symbol("s'_0", definition=Eq.stirling0.rhs.arg.limits[0][1])
    Eq.stirling0 = Eq.stirling0.subs(Eq[-1].reversed)
    Eq << identity(s0_quote).definition
    Eq << Eq[-2].subs(Eq[-1].reversed)
    s0_definition = Eq[-1]

    s1 = Symbol('s1', definition=Eq.stirling1.rhs.arg)
    Eq << identity(s1).definition
    s1_quote = Symbol("s'_1", definition=Eq.stirling1.rhs.arg.limits[0][1])
    Eq.stirling1 = Eq.stirling1.subs(Eq[-1].reversed)
    Eq << identity(s1_quote).definition
    Eq << Eq[-2].subs(Eq[-1].reversed)

    e = Symbol('e', dtype=dtype.integer.set)
    s0_ = image_set(e, Union(e, {n.set}), s0)

    plausible0 = Subset(s0_, s2, plausible=True)
    Eq << plausible0

    Eq << Eq[-1].definition

    Eq << Eq[-1].this.limits[0][1].subs(s0_definition)
    Eq << Eq[-1].subs(Eq.s2_definition)
    s0_plausible = Eq[-1]

    Eq.s2_quote_definition = s2_quote.assertion()
    Eq << s0_quote.assertion()
    Eq << s1_quote.assertion()
    s1_quote_definition = Eq[-1]

    Eq << Eq[-2].split()
    x_abs_positive = Eq[-3]
    x_abs_sum = Eq[-2]
    x_union_s0 = Eq[-1]

    i = Eq[-1].lhs.limits[0][0]
    x = Eq[-1].variable.base

    Eq << Equality.define(x[k], {n})
    x_k_definition = Eq[-1]

    Eq << Eq[-1].union(Eq[-2])
    x_union = Eq[-1]

    Eq << x_k_definition.set

    Eq << Eq[-1].union(x[:k].set)

    Eq << s0_plausible.subs(Eq[-1].reversed)

    Eq << Eq[-1].definition.definition

    Eq << x_k_definition.abs()

    Eq << Eq[-1].subs(1, 0)

    Eq << x_abs_sum + Eq[-2]

    Eq << (x_abs_positive & Eq[-2])

    Eq << (x_union & Eq[-1] & Eq[-2])

    assert len(Eq.plausibles_dict) == 1

    x_tuple = s1_quote_definition.limits[0][0]

    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = s1_quote_definition.split()

    j = Symbol('j', integer=True, domain=Interval(0, k))

    x_quote = IndexedBase("x'", (k + 1,), dtype=dtype.integer,
                     definition=Ref[i](Piecewise((Union(x_tuple[i], {n}) , Equality(i, j)), (x_tuple[i], True))))

    Eq.x_quote_definition = Equality.by_definition_of(x_quote)

    Eq.x_quote_set_in_s2 = Subset(image_set(x_tuple, Union[i:0:k](x_quote[i].set), s1_quote), s2, plausible=True)

    Eq << Eq.x_quote_set_in_s2.definition

    plausible1_simplified = Eq[-1]

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].definition.definition

    Eq << Union[i:0:k](Eq.x_quote_definition)

    x_quote_union = Eq[-1].subs(Eq.x_union_s1)
    Eq << x_quote_union

    Eq << Eq.x_quote_definition.abs()
    x_quote_abs = Eq[-1]

    Eq << Sum[i:0:k](Eq[-1])

    Eq << discrete.sets.union.inequality.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.x_abs_sum_s1)

    Eq << x_quote_union.abs()
    x_quote_union_abs = Eq[-1]

    u = Eq[-1].lhs.arg
    Eq << discrete.sets.union_comprehension.inequality.apply(u.function, *u.limits)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-4].subs(Eq[-1])
    SqueezeTheorem = Eq[-1]

    Eq << x_quote_abs.split()

    Eq << discrete.sets.union.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq[-1].subs(Eq.x_abs_positive_s1.limits_subs(i, j))

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-4].subs(Eq.x_abs_positive_s1)

    Eq << (Eq[-1] & Eq[-2])

    Eq << (x_quote_union & SqueezeTheorem & Eq[-1])

    assert len(Eq.plausibles_dict) == 1
    Eq.x_quote_definition = Ref[i](Eq.x_quote_definition)

    A = IndexedBase("A", (k + 1,), dtype=dtype.integer.set.set, definition=Ref[j](Eq.x_quote_set_in_s2.args[0]))

    Eq.A_definition = Equality.by_definition_of(A)

    Eq << Eq.x_quote_set_in_s2.subs(Eq.A_definition.reversed)

    Eq << Union[j](Eq[-1])

    B = Symbol("B", dtype=dtype.integer.set.set, definition=plausible0.args[0])

    Eq.B_definition = identity(B).definition

    Eq << plausible0.subs(Eq.B_definition.reversed)

    Eq << Eq[-3].union(Eq[-1])
    
#     Eq << identity(s2).bisect(ConditionSet(e, Contains({n}, e), s2))
    Eq << identity(s2).bisect(conditionset(e, Contains({n}, e), s2))

    Eq.subset_B = Subset(Eq[-1].rhs.args[0], Eq[-2].lhs.args[0], plausible=True)  # unproven
    Eq.supset_B = Supset(Eq[-1].rhs.args[0], Eq[-2].lhs.args[0], plausible=True)  # unproven
    Eq.subset_A = Subset(Eq[-1].rhs.args[1], Union[j](Eq[-2].lhs.args[1]), plausible=True)  # unproven
    Eq.supset_A = Supset(Eq[-1].rhs.args[1], Eq[-2].lhs.args[1], plausible=True)

#     assert discrete.sets.union.inclusion_exclusion_principle.apply(*Eq[-1].rhs.args)
    Eq.s2_abs = Eq[-1].abs()

    assert len(Eq.plausibles_dict) == 5

    Eq << Eq.supset_A.subs(Eq.A_definition)

    Eq << Eq[-1].definition.definition

    Eq << Eq[-1].split()

    notContains = Eq[-1]
    Eq << ~Eq[-1]

    Eq << Eq[-1].definition

    Eq << Eq.x_quote_definition[j]

    Eq << Eq[-1].intersect(Eq[-2].reversed)

    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(*Eq[-1].lhs.args)

    Eq << Eq[-1].subs(Eq[-2])

    Eq.set_size_inequality = Eq[-1].subs(1, 0)

    Eq << x_quote_union.this.function.lhs.bisect(domain={i, j})

    Eq << discrete.sets.union.inequality.apply(*Eq[-1].lhs.args)

    Eq << discrete.sets.union_comprehension.inequality.apply(*Eq[-2].lhs.args[0].args)

    Eq << Eq[-2].subs(Eq[-1]) + Eq.set_size_inequality

    Eq << Eq[-1].simplifier(deep=True)

    Eq << Eq[-1].subs(x_quote_union_abs)

    Eq << Eq[-1].subs(SqueezeTheorem)

    Eq << (notContains & plausible1_simplified)

    assert len(Eq.plausibles_dict) == 4

    Eq << Eq.supset_B.subs(Eq.B_definition)

    Eq << Eq[-1].definition.definition

    assert len(Eq.plausibles_dict) == 3

    Eq << Eq.subset_B.subs(Eq.B_definition)

    Eq << Eq[-1].definition.definition

    Eq.subset_B_definition = Eq[-1] - {n.set}

    num_plausibles = len(Eq.plausibles_dict)

    Eq.plausible_notcontains = Forall(NotContains({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].definition

    Eq << x_union_s0.union(Eq[-1].reversed).simplifier(deep=True)

    Eq << Eq[-1].subs(x_union_s0)

    assert num_plausibles == len(Eq.plausibles_dict)

    Eq << Eq.plausible_notcontains.apply(axiom.discrete.sets.intersect.emptyset)

    Eq.s0_complement_n = Eq[-1].apply(axiom.discrete.sets.intersect.complement)

    Eq << Eq.subset_B_definition.subs(Eq.s0_complement_n)

    s2_n = Symbol('s_{2, n}', definition=Eq[-1].limits[0][1]);

    Eq.s2_n_definition = identity(s2_n).definition

    Eq << s2_n.assertion()

    Eq << Eq[-1].split()

    Eq << Eq[-2].subs(Eq.s2_definition)

    Eq.s2_n_assertion = Eq[-1].definition

    Eq << Eq[-2].subs(Eq.s2_n_assertion)

    Eq << Eq[-1].definition

    Eq.x_j_definition = Eq[-1].limits_subs(Eq[-1].variable, j).reversed

    Eq.x_abs_positive_s2, Eq.x_abs_sum_s2, Eq.x_union_s2 = Eq.s2_quote_definition.split()

    Eq << Eq.x_union_s2 - Eq.x_j_definition

    Eq << Eq[-1].this.function.lhs.args[0].bisect(domain={j})

    x_tilde = IndexedBase(r"\tilde{x}", (k,), dtype=dtype.integer,
                     definition=Ref[i](Piecewise((x[i], i < j), (x[i + 1], True))))

    Eq.x_tilde_definition = Equality.by_definition_of(x_tilde)

    Eq << Union[i:0:k - 1](Eq.x_tilde_definition)

    Eq << Eq[-1].this.rhs.args[1].limits_subs(i, i - 1)

    Eq.x_tilde_union = Eq[-1].subs(Eq[-3])

    Eq.x_tilde_abs = Eq.x_tilde_definition.abs()

    Eq << Sum[i:0:k - 1](Eq.x_tilde_abs)

    Eq << Eq[-1].this.rhs.args[1].limits_subs(i, i - 1)

    Eq.x_tilde_abs_sum = Eq[-1].subs(Eq.x_abs_sum_s2, Eq.x_j_definition.abs())

    Eq << Eq.x_tilde_abs.split()

    Eq << Eq[-2].subs(Eq.x_abs_positive_s2)

    Eq << Eq[-2].subs(Eq.x_abs_positive_s2.limits_subs(i, i + 1))

    Eq << (Eq[-1] & Eq[-2])

    Eq << (Eq[-1] & Eq.x_tilde_abs_sum & Eq.x_tilde_union)

    Eq << Eq[-1].func(Contains(x_tilde, s0_quote), *Eq[-1].limits, plausible=True)

    Eq << Eq[-1].definition

    Eq.x_tilde_set_in_s0 = Eq[-2].func(Contains(UnionComprehension.construct_finite_set(x_tilde), s0), *Eq[-2].limits, plausible=True)

    Eq << Eq.x_tilde_set_in_s0.subs(s0_definition)

    Eq << Eq[-1].definition

    Eq << Union[i:0:k - 1](Eq.x_tilde_definition.set)

    Eq << Eq[-1].subs(Eq.x_j_definition)

    Eq << Eq[-1].subs(Eq.s2_n_assertion.reversed)
#     assert Eq.x_tilde_set_in_s0.function.lhs == Eq[-1].function.function.function.lhs
    Eq << Eq.x_tilde_set_in_s0.subs(Eq[-1])

    Eq << Eq[-1].this.limits[0].subs(Eq.s2_n_definition)

    assert len(Eq.plausibles_dict) == 2

    Eq << Eq.subset_A.subs(Eq.A_definition)

    Eq << Eq[-1].definition.definition.definition

    s2_hat_n = Symbol("\hat{s}_{2, n}", definition=Eq[-1].limits[0][1])

    Eq << identity(s2_hat_n).definition

    Eq.s2_hat_n_assertion = Eq[-2].this.limits[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.as_image_set()

    s2_quote_n = Symbol("s'_{2, n}", definition=Eq[-1].rhs.limits[0][1])

    assert s2_quote_n in s2_quote
    assert Supset(s2_quote, s2_quote_n)

    Eq << identity(s2_quote_n).definition

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])
#     Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])

    Eq << s2_quote_n.assertion()

    Eq.x_abs_positive_s2_n, Eq.n_not_in_x, Eq.x_abs_sum_s2_n, Eq.x_union_s2_n = Eq[-1].split()

    Eq << Eq.n_not_in_x.definition

    Eq.x_j_inequality = Eq[-1].limits_subs(i, j)

    Eq << Eq.x_union_s2_n.func(Contains(n, Eq.x_union_s2_n.lhs), *Eq.x_union_s2_n.limits, plausible=True)

    Eq << Eq[-1].subs(Eq.x_union_s2_n)

    Eq << Eq[-1].definition

    x_hat = IndexedBase(r"\hat{x}", (oo,), dtype=dtype.integer,
                     definition=Ref[i](Piecewise((x_tuple[i] - {n} , Equality(i, j)), (x_tuple[i], True))))

    Eq.x_hat_definition = Equality.by_definition_of(x_hat)

    Eq << Eq[-1].this.function.limits_subs(i, j)

    Eq.x_j_subset = Eq[-1].apply(discrete.sets.contains.subset)

    Eq << Eq.x_j_subset.apply(discrete.sets.complement.emptyset, Eq.x_j_inequality)

    Eq << Eq[-1].apply(discrete.sets.emptyset.strict_greater_than)  # -4

    Eq.x_hat_abs = Eq.x_hat_definition.abs()

    Eq << Eq.x_hat_abs.split()  # -2, -3

    Eq << Eq[-1].subs(Eq.x_abs_positive_s2_n)  # -1

    Eq << Eq[-3].subs(Eq[-4])

    Eq.x_hat_abs_positive = Eq[-1] & Eq[-2]

    Eq.x_hat_union = Union[i:0:k](Eq.x_hat_definition)

    Eq.x_union_complement = Eq.x_union_s2_n - {n}

    Eq << Eq.x_union_s2_n.abs().subs(Eq.x_abs_sum_s2_n.reversed).apply(discrete.sets.union_comprehension.nonoverlapping)

    Eq << Eq[-1].limits_subs(Eq[-1].variables[1], j).limits_subs(Eq[-1].variable, i)

    Eq.x_complement_n = Eq[-1].apply(discrete.sets.complement.subset, Eq.x_j_subset)

    Eq << Eq.x_complement_n.this.function.function.union_comprehension(*Eq.x_complement_n.function.function.limits)

    Eq << Eq.x_hat_union.subs(Eq[-1].reversed)

    Eq.x_hat_union = Eq[-1].subs(Eq.x_union_complement)

    Eq << Sum[i:0:k](Eq.x_hat_abs).subs(Eq.x_abs_sum_s2_n)

    Eq << Eq.x_j_subset.apply(discrete.sets.subset.complement)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << (Eq[-1] & Eq.x_hat_abs_positive & Eq.x_hat_union)

    function = Contains(x_hat[:k + 1], s1_quote)
    function = Eq[-1].function.func(function, *Eq[-1].function.limits)

    Eq.x_hat_in_s1 = Eq[-1].func(function, *Eq[-1].limits, plausible=True)

    Eq << Eq.x_hat_in_s1.definition

    Eq << Eq.x_hat_definition.split()

    Eq << Eq[-1].subs(Eq.x_complement_n.reversed)

    Eq << (Eq[-1] & Eq[-3])

    Eq << Eq[-1].this.function.function.reference(*Eq[-1].function.function.limits)

    Eq << Eq.x_hat_in_s1.subs(Eq[-1])

    Eq << Eq.s2_hat_n_hypothesis.strip().strip()

    Eq << Eq[-1].subs(Eq.x_quote_definition)

    Eq.equation = Eq[-1] - {n}

    Eq << Eq.x_union_s1.intersect({n})

    Eq.nonoverlapping_s1_quote = Eq[-1].apply(discrete.sets.union_comprehension.intersect)

    Eq << Eq.nonoverlapping_s1_quote.apply(discrete.sets.intersect.complement, reverse=True)

    Eq << Eq.equation.subs(Eq[-1])

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[-1].function.variable)

    Eq << Eq[-1].this.function.function.reference(*Eq[-1].function.function.limits)

    assert len(Eq.plausibles_dict) == 1

    Eq.s2_abs_plausible = Eq[0].subs(Eq.stirling2, Eq.stirling0, Eq.stirling1)

    Eq.supset_A = Eq.supset_A.union_comprehension((j,))

    Eq << Eq.supset_A.subs(Eq.subset_A)

    Eq << Eq.supset_B.subs(Eq.subset_B)

    Eq.s2_abs = Eq.s2_abs.subs(Eq[-1], Eq[-2])

    Eq.B_assertion = B.assertion()

    Eq << Eq.B_assertion - {n.set}

    Eq << Eq[-1].subs(Eq.s0_complement_n).limits_subs(Eq[-1].variable, Eq[-1].function.variable)

    Eq.s0_supset = Supset(s0, image_set(e, e - {n.set}, B), plausible=True)

    Eq << Eq.s0_supset.simplifier()

    Eq.s0_subset = Subset(s0, image_set(e, e - {n.set}, B), plausible=True)

    Eq << Eq.s0_subset.definition.definition

    Eq << Eq[-1].union({n.set})

    Eq << B.assertion(reverse=True)

    Eq << Eq.B_assertion.intersect({n.set}).limits_subs(Eq.B_assertion.variable, Eq.B_assertion.function.variable)

    Eq << Eq[-1].union(Eq[-1].variable)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-4] - {n.set}

    Eq << Eq.s0_complement_n.limits_subs(Eq.s0_complement_n.variable, Eq[-1].variable)

    Eq << Eq[-1].subs(Eq.s0_complement_n)

    Eq << Eq.s0_supset.subs(Eq.s0_subset)

    Eq << discrete.sets.union_comprehension.inequality.apply(*Eq[-1].rhs.args)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << discrete.sets.union_comprehension.inequality.apply(*Eq.B_definition.rhs.args)

    Eq << Eq[-1].subs(Eq.B_definition.reversed)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq.s2_abs.subs(Eq[-1].reversed)

    assert len(Eq.plausibles_dict) == 2

    Eq.A_union_abs = Eq.s2_abs_plausible.subs(Eq[-1])

    assert len(Eq.plausibles_dict) == 3

#     Eq << identity(Eq[-1].lhs.arg).subs(Eq.A_definition)

    A_quote = IndexedBase("A'", (k + 1,), dtype=dtype.integer.set.set, definition=Ref[j](Eq.A_definition.rhs.function))

    Eq.A_quote_definition = identity(A_quote).definition

    Eq.A_definition_simplified = Eq.A_definition.subs(Eq.A_quote_definition[j].reversed)

    from sympy import S

    j_quote = Symbol("j'", integer=True)

    Eq.nonoverlapping = Forall(Equality(A_quote[j_quote] & A_quote[j], S.EmptySet), *((j_quote, Interval(0, k, integer=True) - {j}),) + Eq.A_definition_simplified.rhs.limits, plausible=True)

    assert len(Eq.plausibles_dict) == 4

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].apply(discrete.sets.intersect.overlapping)

    Eq << Eq[-1].subs(Eq.A_quote_definition[j])

    Eq << Eq[-1].subs(Eq.A_quote_definition[j_quote])

    Eq << Eq[-1].apply(discrete.sets.equality.supset)

    Eq << Eq[-1].this.function.subs(Eq[-1].function.variable, Eq[-1].variable)

    Eq << Eq[-1].definition

    Eq << Eq[-1].subs(Eq.x_quote_definition)

    Eq << Eq[-1].split()

    Eq << Eq[-1].intersect({n})

    Eq << Eq[-1].subs(Eq.nonoverlapping_s1_quote)

    assert len(Eq.plausibles_dict) == 3

    Eq << Eq.nonoverlapping.union_comprehension(Eq.nonoverlapping.limits[1])

    Eq << Eq[-1].this.function.lhs.as_two_terms()

    Eq << Eq.A_definition_simplified.subs(j, j_quote)

    Eq << Eq[-2].subs(Eq[-1].reversed, Eq.A_definition_simplified.reversed)

    Eq << Equality(Eq.A_union_abs.lhs, Sum[j](abs(A[j])), plausible=True)

    Eq << Eq[-1].apply(discrete.sets.union_comprehension.nonoverlapping)

    Eq << Eq.A_union_abs.subs(Eq[-1])
    return
    e = A[j].element_symbol()
    A_hat_j = Symbol("\hat{A}_{j}", definition=Union[e: A[j]](e.list_set))

    Eq << identity(A_hat_j).definition

    Eq << Eq.A_definition.rhs.assertion()

    Eq << Eq[-1].subs(Eq.A_definition.reversed)

    Eq << Eq[-1].abs()

    i_quote = Symbol("i'", domain=Interval(0, k, integer=True))
    Eq << Forall(Unequality(x_quote[i], x_quote[i_quote]), (i, Interval(0, k, integer=True) - {i_quote}), plausible=True)

    Eq << ~Eq[-1]

    Eq << Eq[-1].subs(Eq.x_quote_definition[i_quote], Eq.x_quote_definition[i])

    Eq << Eq[-1].split()

    Eq << Eq[-1].split()


if __name__ == '__main__':
    prove(__file__)

