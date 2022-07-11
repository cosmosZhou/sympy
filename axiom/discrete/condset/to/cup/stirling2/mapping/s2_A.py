from util import *


@apply
def apply(n, k, s2=None, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    j = Symbol(domain=Range(k + 1))
    if s2 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s2 = Symbol(Cup[x[:k + 1]:Stirling.conditionset(n + 1, k + 1, x)](x[:k + 1].cup_finiteset().set))

    e = Symbol(**s2.etype.dict)
    if A is None:
        x = s2.definition.variable.base
        i = Symbol(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol(Lamda[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol(Lamda[j](Cup[x[:k + 1]:s1_quote]({x_quote.cup_finiteset()})))

    return Equal(conditionset(e, NotElement({n}, e), s2), Cup[j](A[j]))


@prove(proved=False)
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s2_quote = Symbol('s_quote_2', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s2_quote.this.definition

    Eq.s2_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s2_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    s1_quote = Eq[2].lhs
    Eq << sets.imply.all.conditionset.apply(s1_quote)

    i = Eq[1].lhs.indices[0]
    x_slice = Eq[-1].limits[0][0]
    x = x_slice.base
    Eq.x_abs_positive_s1 = algebra.all_et.imply.all.apply(Eq[-1])

    Eq.x_abs_sum_s1 = algebra.all_et.imply.all.apply(Eq[-1], 1)

    Eq.x_union_s1 = algebra.all_et.imply.all.apply(Eq[-1], 2)

    j = Symbol(domain=Range(k + 1))
    x_quote = Eq[1].lhs.base
    Eq.x_quote_set_in_s2 = Subset(imageset(x_slice, Cup[i:k + 1](x_quote[i].set), s1_quote), Eq[0].lhs, plausible=True)

    Eq << sets.subset.given.all_el.apply(Eq.x_quote_set_in_s2)

    Eq << Eq[-1].subs(Eq.s2_definition)

    Eq << Eq[-1].this.expr.apply(sets.el.given.el.split.imageset)

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << Eq[-1].this.expr.args[0].simplify()

    Eq << sets.eq.imply.eq.cup.apply(Eq[1], (i, 0, k + 1))

    Eq.x_quote_union = algebra.all_eq.cond.imply.all.subs.apply(Eq.x_union_s1, Eq[-1])

    Eq << Eq[1].apply(sets.eq.imply.eq.card)

    x_quote_abs = Eq[-1]
    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (i, 0, k + 1))

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << algebra.eq.le.imply.le.subs.apply(Eq[-2], Eq[-1])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_union.this.expr.apply(sets.eq.imply.eq.card)

    x_quote_union_abs = Eq[-1]
    u = Eq[-1].lhs.arg
    Eq << sets.imply.le.cup.apply(u.expr, *u.limits)

    Eq << Eq[-2].this.expr.apply(algebra.eq.le.imply.ge.subs, Eq[-1])

    Eq.SqueezeTheorem = Eq[-4] & Eq[-1]

    Eq << algebra.eq_piece.imply.ou.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)

    Eq << Eq[-2].apply(algebra.cond.imply.all.restrict, (i, Unequal(i, j)))

    Eq << sets.imply.ge.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.expr.apply(algebra.gt.ge.imply.gt.transit, Eq[-1])

    Eq.xj_is_positive = Eq[-1].subs(Eq[-4].reversed)

    Eq << algebra.all.all.imply.all_et.apply(Eq.x_abs_positive_s1, Eq[-3].reversed)

    Eq.xi_is_positive = Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.transit)

    Eq.xi_all_is_positive = Eq.xi_is_positive.apply(algebra.all.given.all.limits.delete, index=0)

    Eq << Eq.xi_all_is_positive.this.expr.apply(algebra.cond.given.et.all, cond=Equal(i, j))

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << Eq[-1].apply(algebra.all.given.all_ou.limits.delete, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_complement.given.ou, simplify=None)

    Eq << Eq[-1].this.find(Greater).apply(algebra.cond.given.ou.domain_defined, wrt=i, simplify=None)

    Eq << Eq.xi_is_positive.apply(algebra.all.imply.all_ou.limits.delete, simplify=None)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin_complement.imply.ou, simplify=None)

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq.xi_all_is_positive

    Eq.x_quote_definition = Eq[1].apply(algebra.eq.imply.eq.lamda, (i, 0, k + 1), simplify=False)

    Eq.subset_A = Subset(Eq[4].lhs, Eq[4].rhs, plausible=True)

    Eq.supset_A = Supset(Eq[4].lhs, Eq[3].lhs, plausible=True)

    Eq << Eq.supset_A.subs(Eq[3])

    Eq << sets.supset.given.all_el.apply(Eq[-1])

    Eq << Eq[-1].this.expr.simplify()

    Eq << algebra.all_et.given.et.all.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.el_cup.imply.any_el)

    Eq << Eq.x_quote_definition[j]

    Eq << Eq[-2].reversed.this.expr.apply(sets.eq.eq.imply.eq.intersect, Eq[-1])

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(*Eq[-1].lhs.args)

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-2], Eq[-1])

    Eq.set_size_inequality = Eq[-1].this.expr.apply(algebra.eq.lt.imply.lt.subs, Less(Eq[-1].expr.rhs, Eq[-1].expr.rhs + 1, plausible=True))

    Eq << Eq.x_quote_union.this.expr.lhs.apply(sets.cup.to.union.split, cond={i, j})

    Eq << sets.imply.le.union.apply(*Eq[-1].lhs.args)

    Eq << sets.imply.le.cup.apply(*Eq[-2].lhs.args[0].args)

    Eq << algebra.le.le.imply.le.subs.apply(Eq[-2], Eq[-1])

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq.set_size_inequality)

    Eq << Eq[-1].this.expr.apply(algebra.lt.le.imply.lt.add)

    return
    Eq << Eq[-1].this(var=Eq[-1].variables[0]).find(Sum).simplify()
    Eq << Eq[-1].this(var=Eq[-1].variables[0]).expr.rhs.find(Cup).simplify()
    Eq << algebra.all.any.imply.any_et.apply(x_quote_union_abs, Eq[-1])
    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)
    Eq << algebra.all.any.imply.any_et.apply(Eq.SqueezeTheorem, Eq[-1])
    Eq << Eq.subset_A.subs(Eq[3])
    Eq << sets.subset.given.all_el.apply(Eq[-1])
    s2_hat_n = Symbol("\hat{s}_{2, n}", conditionset(*Eq[-1].limits[0]))
    Eq << sets.all.given.all.conditionset.split.baseset.apply(Eq[-1], simplify=False, s=s2_hat_n)
    Eq.s2_hat_n_assertion = Eq[-1].this.expr.apply(sets.element.given.any_contains.split.cup)
    Eq << s2_hat_n.this.definition
    Eq << Eq[-1].this.rhs.apply(sets.conditionset.to.imageset)
    s2_quote_n = Symbol("s'_{2, n}", conditionset(Eq[-1].rhs.variable, Eq[-1].rhs.limits[0][1]))
    assert s2_quote_n in s2_quote
    assert Supset(s2_quote, s2_quote_n)
    Eq << s2_quote_n.this.definition
    Eq << imageset(Eq[-2].rhs.variable, Eq[-2].rhs.expr.arg, s2_quote_n).this.subs(Eq[-1]).subs(Eq[-2].reversed).reversed
    Eq.s2_hat_n_hypothesis = Eq.s2_hat_n_assertion.this.limits[0].subs(Eq[-1])
    Eq << sets.imply.all.conditionset.apply(s2_quote_n)
    Eq << Eq[-1].this.expr.apply(sets.eq.eq.all_is_positive.notcontains.imply.eq.stirling2, s1=s1_quote)
    Eq << algebra.all_any.imply.all_any.limits_swap.apply(Eq[-1])
    Eq << Eq.s2_hat_n_hypothesis.this.expr.expr.apply(sets.eq.given.eq.cup_finiteset)
    Eq << Eq[-1].subs(Eq.x_quote_definition)
    Eq.supset_A = sets.supset.imply.supset.cup.lhs.apply(Eq.supset_A, (j,), simplify=False)
    Eq <<= Eq.supset_A & Eq.subset_A


if __name__ == '__main__':
    run()

# created on 2020-10-03
