from sympy.core.symbol import Symbol, dtype
from sympy.core.relational import Equality, StrictLessThan, Unequality
from axiom.utility import plausible
from sympy.functions.combinatorial.numbers import Stirling
from sympy.sets.sets import image_set, Interval
from sympy.sets.contains import Subset, Supset, Contains, NotContains
from sympy.functions.elementary.piecewise import Piecewise
from axiom import sets, algebre
from sympy.sets.conditionset import conditionset
from sympy import UNION, LAMBDA
from sympy.core.numbers import oo

@plausible
def apply(n, k, s2=None, A=None):
    j = Symbol.j(domain=Interval(0, k, integer=True))
    if s2 is None:    
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s2 = Symbol.s2(definition=UNION[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].set_comprehension().set))

    e = Symbol.e(**s2.etype.dict)
    if A is None:
        x = s2.definition.variable.base
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", definition=Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", definition=LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equality(i, j)), (x[i], True))))
        A = Symbol.A(definition=LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        

    return Equality(conditionset(e, NotContains({n}, e), s2), UNION[j](A[j]))


from axiom.utility import check


@check
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    s2_quote = Symbol.s_quote_2(definition=Eq[0].rhs.limits[0][1])
    Eq << s2_quote.this.definition

    Eq.s2_definition = Eq[0].subs(Eq[-1].reversed)

    s1_quote = Eq[2].lhs 

    Eq << sets.imply.forall.conditionset.apply(s1_quote)

    i = Eq[1].lhs.indices[0]
    x_slice = Eq[-1].limits[0][0]
    x = x_slice.base

    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = Eq[-1].split()

    j = Symbol.j(domain=Interval(0, k, integer=True))

    x_quote = Eq[1].lhs.base

    Eq.x_quote_set_in_s2 = Subset(image_set(UNION[i:0:k](x_quote[i].set), x_slice, s1_quote), Eq[0].lhs, plausible=True)

    Eq << Eq.x_quote_set_in_s2.definition

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].definition.definition
    Eq << Eq[-1].this.function.args[0].simplify()
    
    Eq << Eq[1].union_comprehension((i, 0, k))

    x_quote_union = Eq[-1].subs(Eq.x_union_s1)
    Eq << x_quote_union

    Eq << Eq[1].abs()
    x_quote_abs = Eq[-1]
    
    Eq << Eq[-1].sum((i, 0, k))

    Eq << sets.imply.less_than.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq.x_abs_sum_s1)

    Eq << x_quote_union.abs()
    x_quote_union_abs = Eq[-1]

    u = Eq[-1].lhs.arg
    Eq << sets.imply.less_than.union_comprehension.apply(u.function, *u.limits)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-4].subs(Eq[-1])
    SqueezeTheorem = Eq[-1]

    Eq << algebre.equality.imply.ou.two.apply(x_quote_abs)
    
    Eq << Eq[-1].subs(i, j)
    
    Eq << Eq[-2].forall((i, Unequality(i, j)))

    Eq << sets.imply.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq[-1].subs(Eq.x_abs_positive_s1.limits_subs(i, j))

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[-4].subs(Eq.x_abs_positive_s1)

    Eq << (Eq[-1] & Eq[-2])

    Eq << (x_quote_union & SqueezeTheorem & Eq[-1])

    Eq.x_quote_definition = Eq[1].reference((i, 0, k))

    Eq.subset_A = Subset(Eq[4].lhs, Eq[4].rhs, plausible=True)
    Eq.supset_A = Supset(Eq[4].lhs, Eq[3].lhs, plausible=True)

    Eq << Eq.supset_A.subs(Eq[3])

    Eq << Eq[-1].definition.definition

    Eq << Eq[-1].split()

    notContains = Eq[-1]
    Eq << ~Eq[-1]

    Eq << Eq[-1].definition

    Eq << Eq.x_quote_definition[j]

    Eq << Eq[-1].intersect(Eq[-2].reversed)

    Eq << sets.imply.equality.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args)
  
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq.set_size_inequality = Eq[-1].subs(StrictLessThan(Eq[-1].function.rhs, Eq[-1].function.rhs + 1, plausible=True))
    
    Eq << x_quote_union.this.function.lhs.bisect({i, j})

    Eq << sets.imply.less_than.union.apply(*Eq[-1].lhs.args)

    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[-2].lhs.args[0].args)

    Eq << Eq[-2].subs(Eq[-1]) + Eq.set_size_inequality
    
    Eq << Eq[-1].this(shape=()).function.rhs.args[-1].simplify()
    
    Eq << Eq[-1].this(shape=()).function.rhs.args[0].arg.simplify()

    Eq << Eq[-1].subs(x_quote_union_abs)

    Eq << Eq[-1].subs(SqueezeTheorem)

    Eq << Eq.subset_A.subs(Eq[3])

    Eq << Eq[-1].definition.definition

    s2_hat_n = Symbol("\hat{s}_{2, n}", definition=Eq[-1].limits[0][1])

    Eq << s2_hat_n.this.definition

    Eq.s2_hat_n_assertion = Eq[-2].this.limits[0].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.as_image_set()

    s2_quote_n = Symbol("s'_{2, n}", definition=Eq[-1].rhs.limits[0][1])

    assert s2_quote_n in s2_quote
    assert Supset(s2_quote, s2_quote_n)

    Eq << s2_quote_n.this.definition

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])

    Eq << sets.imply.forall.conditionset.apply(s2_quote_n)

    Eq.n_not_in_x, Eq.x_abs_positive_s2_n, Eq.x_abs_sum_s2_n, Eq.x_union_s2_n = Eq[-1].split()

    Eq << Eq.n_not_in_x.apply(sets.notcontains.imply.forall_notcontains)

    Eq.x_j_inequality = Eq[-1].limits_subs(i, j)

    Eq << Eq.x_union_s2_n.func(Contains(n, Eq.x_union_s2_n.lhs), *Eq.x_union_s2_n.limits, plausible=True)

    Eq << Eq[-1].subs(Eq.x_union_s2_n)

    Eq << Eq[-1].definition

    x_hat = Symbol(r"\hat{x}", shape=(oo,), etype=dtype.integer,
                     definition=LAMBDA[i](Piecewise((x_slice[i] - {n} , Equality(i, j)), (x_slice[i], True))))

    Eq.x_hat_definition = x_hat.equality_defined()

    Eq << Eq[-1].this.function.limits_subs(i, j)

    Eq.x_j_subset = Eq[-1].apply(sets.contains.imply.subset, simplify=False)    

    Eq << Eq.x_j_subset.apply(sets.is_nonemptyset.subset.imply.is_nonemptyset, Eq.x_j_inequality, simplify=False)

    Eq.x_j_abs_positive = Eq[-1].apply(sets.is_nonemptyset.imply.is_positive)

    Eq.x_hat_abs = Eq.x_hat_definition.abs()

    Eq << algebre.equality.imply.ou.two.apply(Eq.x_hat_abs)
    
    Eq << Eq[-1].subs(i, j)
    Eq << Eq[-2].forall((i, Unequality(i, j)))
    
    Eq << Eq[-1].subs(Eq.x_abs_positive_s2_n)  # -1

    Eq << Eq[-3].subs(Eq.x_j_abs_positive)

    Eq.x_hat_abs_positive = Eq[-1] & Eq[-2]

    Eq.x_hat_union = Eq.x_hat_definition.union_comprehension((i, 0, k))
    Eq.x_union_complement = Eq.x_union_s2_n - {n}

    Eq << Eq.x_union_s2_n.abs().subs(Eq.x_abs_sum_s2_n.reversed).apply(sets.equality.imply.forall_equality.nonoverlapping)

    Eq << Eq[-1].limits_subs(Eq[-1].variables[1], j).limits_subs(Eq[-1].variable, i)

    Eq.x_complement_n = Eq[-1].apply(sets.is_emptyset.subset.imply.equality, Eq.x_j_subset)

    Eq << Eq.x_complement_n.this.function.function.union_comprehension(*Eq.x_complement_n.function.function.limits)

    Eq << Eq.x_hat_union.subs(Eq[-1].reversed)

    Eq.x_hat_union = Eq[-1].subs(Eq.x_union_complement)

    Eq << Eq.x_hat_abs.sum((i, 0, k)).subs(Eq.x_abs_sum_s2_n)

    Eq << Eq.x_j_subset.apply(sets.subset.imply.equality.complement)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << (Eq[-1] & Eq.x_hat_abs_positive & Eq.x_hat_union)

    function = Contains(x_hat[:k + 1], s1_quote)
    function = Eq[-1].function.func(function, *Eq[-1].function.limits)

    Eq.x_hat_in_s1 = Eq[-1].func(function, *Eq[-1].limits, plausible=True)

    Eq << Eq.x_hat_in_s1.definition

    Eq << algebre.equality.imply.ou.two.apply(Eq.x_hat_definition)    
    
    Eq << Eq[-1].subs(i, j)
    Eq << Eq[-2].forall((i, Unequality(i, j)))
    
    Eq <<= Eq[-1] & Eq.x_complement_n.reversed

    Eq << (Eq[-1] & Eq[-3])

    Eq << Eq[-1].this.function.function.reference(*Eq[-1].function.function.limits)

    Eq << Eq.x_hat_in_s1.subs(Eq[-1])

    Eq << Eq.s2_hat_n_hypothesis.strip().strip()

    Eq << Eq[-1].subs(Eq.x_quote_definition)

    Eq.equation = Eq[-1] - {n}

    Eq << Eq.x_union_s1.intersect({n})

    Eq.nonoverlapping_s1_quote = Eq[-1].apply(sets.is_emptyset.imply.forall_is_emptyset.intersect)

    Eq.xi_complement_n = Eq.nonoverlapping_s1_quote.apply(sets.is_emptyset.imply.equality.complement, reverse=True)

    Eq << Eq.equation.subs(Eq.xi_complement_n)

    a = Eq[-1].variable
    b = Symbol.b(**a.type.dict)
    
    Eq << Eq[-1].limits_subs(a, b)
    
    Eq << Eq[-1].this.function.subs(x[:k + 1], a)
    
    Eq << Eq[-1].limits_subs(b, x[:k + 1])
    
    Eq << Eq[-1].this.function.function.reference((i, 0, k))
    
    Eq.supset_A = sets.supset.imply.supset.apply(Eq.supset_A, (j,), simplify=False)

    Eq << Eq.supset_A.subs(Eq.subset_A)


if __name__ == '__main__':
    prove(__file__)

