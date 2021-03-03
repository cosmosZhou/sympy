from sympy import *
from axiom.utility import prove, apply
from sympy.functions.combinatorial.numbers import Stirling

from axiom import sets, algebre


@apply
def apply(n, k, s2=None, A=None):
    j = Symbol.j(domain=Interval(0, k, integer=True))
    if s2 is None: 
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        s2 = Symbol.s2(UNION[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].set_comprehension().set))

    e = Symbol.e(**s2.etype.dict)
    if A is None:
        x = s2.definition.variable.base
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", LAMBDA[i:k + 1](Piecewise(({n} | x[i], Equality(i, j)), (x[i], True))))
        A = Symbol.A(LAMBDA[j](UNION[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))        

    return Equality(conditionset(e, NotContains({n}, e), s2), UNION[j](A[j]))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    s2_quote = Symbol.s_quote_2(conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s2_quote.this.definition
    
    Eq.s2_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.function.arg, s2_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed
    
    s1_quote = Eq[2].lhs 

    Eq << sets.imply.forall.conditionset.apply(s1_quote)

    i = Eq[1].lhs.indices[0]
    x_slice = Eq[-1].limits[0][0]
    x = x_slice.base

    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = Eq[-1].split()

    j = Symbol.j(domain=Interval(0, k, integer=True))

    x_quote = Eq[1].lhs.base

    Eq.x_quote_set_in_s2 = Subset(imageset(x_slice, UNION[i:k + 1](x_quote[i].set), s1_quote), Eq[0].lhs, plausible=True)

    Eq << sets.subset.given.forall_contains.apply(Eq.x_quote_set_in_s2)

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].this.function.apply(sets.contains.given.contains.where.imageset)
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << Eq[-1].this.function.args[0].simplify()
    
    Eq << sets.equal.imply.equal.union_comprehension.apply(Eq[1], (i, 0, k + 1))

    Eq.x_quote_union = Eq[-1].subs(Eq.x_union_s1)

    Eq << Eq[1].apply(algebre.equal.imply.equal.abs)
    x_quote_abs = Eq[-1]
    
    Eq << Eq[-1].apply(algebre.equal.imply.equal.sum, (i, 0, k + 1))

    Eq << sets.imply.less_than.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << algebre.equal.less_than.imply.less_than.subs.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].subs(Eq.x_abs_sum_s1)

    Eq << Eq.x_quote_union.apply(algebre.equal.imply.equal.abs)    
    x_quote_union_abs = Eq[-1]

    u = Eq[-1].lhs.arg
    Eq << sets.imply.less_than.union_comprehension.apply(u.function, *u.limits)

    Eq << Eq[-2].this.function.apply(algebre.equal.less_than.imply.greater_than.subs, Eq[-1])
    
    Eq.SqueezeTheorem = Eq[-4] & Eq[-1]

    Eq << algebre.equal.imply.ou.two.apply(x_quote_abs)
    
    Eq << Eq[-1].subs(i, j)
    
    Eq << Eq[-2].apply(algebre.condition.imply.forall.minify, (i, Unequality(i, j)))

    Eq << sets.imply.greater_than.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.function.apply(algebre.strict_greater_than.greater_than.imply.strict_greater_than.transit, Eq[-1])

    Eq << Eq[-1].subs(Eq[-4].reversed)

    Eq << Eq.x_abs_positive_s1.subs(Eq[-4].reversed)

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq[-1]

    Eq.x_quote_definition = Eq[1].apply(algebre.equal.imply.equal.lamda, (i, 0, k + 1), simplify=False)

    Eq.subset_A = Subset(Eq[4].lhs, Eq[4].rhs, plausible=True)
    Eq.supset_A = Supset(Eq[4].lhs, Eq[3].lhs, plausible=True)

    Eq << Eq.supset_A.subs(Eq[3])

    Eq << sets.supset.given.forall_contains.apply(Eq[-1])
    
    Eq << Eq[-1].this.function.simplify()

    Eq << Eq[-1].split()

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(sets.contains.imply.exists_contains.where.union_comprehension)
    
    Eq << Eq.x_quote_definition[j]

    Eq << Eq[-2].reversed.apply(sets.equal.equal.imply.equal.intersect, Eq[-1])
    
    Eq << sets.imply.equal.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args)
  
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq.set_size_inequality = Eq[-1].this.function.apply(algebre.equal.strict_less_than.imply.strict_less_than.subs, StrictLessThan(Eq[-1].function.rhs, Eq[-1].function.rhs + 1, plausible=True))
    
    Eq << Eq.x_quote_union.this.function.lhs.bisect({i, j})

    Eq << sets.imply.less_than.union.apply(*Eq[-1].lhs.args)

    Eq << sets.imply.less_than.union_comprehension.apply(*Eq[-2].lhs.args[0].args)

    Eq << algebre.less_than.less_than.imply.less_than.subs.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1] + Eq.set_size_inequality
    
    Eq << Eq[-1].this(shape=()).function.rhs.args[-1].simplify()
    
    Eq << Eq[-1].this(shape=()).function.rhs.args[0].arg.simplify()

    Eq << Eq[-1].subs(x_quote_union_abs)

    Eq << Eq[-1].subs(Eq.SqueezeTheorem)

    Eq << Eq.subset_A.subs(Eq[3])

    Eq << sets.subset.given.forall_contains.apply(Eq[-1])

    s2_hat_n = Symbol("\hat{s}_{2, n}", conditionset(*Eq[-1].limits[0]))

    Eq << sets.forall.given.forall.conditionset.where.baseset.apply(Eq[-1], simplify=False, s=s2_hat_n)

    Eq.s2_hat_n_assertion = Eq[-1].apply(sets.contains.given.exists_contains.where.union_comprehension)
    
    Eq << s2_hat_n.this.definition
    
    Eq << Eq[-1].this.rhs.apply(sets.conditionset.astype.imageset)

    s2_quote_n = Symbol("s'_{2, n}", conditionset(Eq[-1].rhs.variable, Eq[-1].rhs.limits[0][1]))

    assert s2_quote_n in s2_quote
    assert Supset(s2_quote, s2_quote_n)

    Eq << s2_quote_n.this.definition
    
    Eq << imageset(Eq[-2].rhs.variable, Eq[-2].rhs.function.arg, s2_quote_n).this.subs(Eq[-1]).subs(Eq[-2].reversed).reversed
    
    Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])
    
    Eq << sets.imply.forall.conditionset.apply(s2_quote_n)
    
    Eq << Eq[-1].this.function.apply(sets.equal.equal.forall_is_positive.notcontains.imply.equal.stirling2, s1=s1_quote, depth=0)
    
    Eq << algebre.forall_exists.imply.forall_exists.limits_swap.apply(Eq[-1])

    Eq << Eq.s2_hat_n_hypothesis.apply(sets.equal.given.equal.set_comprehension)

    Eq << Eq[-1].subs(Eq.x_quote_definition)
    
    Eq.supset_A = sets.supset.imply.supset.union_comprehension.lhs.apply(Eq.supset_A, (j,), simplify=False)

    Eq <<= Eq.supset_A & Eq.subset_A


if __name__ == '__main__':
    prove(__file__)

