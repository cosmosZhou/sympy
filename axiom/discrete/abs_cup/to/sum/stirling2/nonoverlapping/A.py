from util import *


@apply
def apply(n, k, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    assert k < n
    j = Symbol(domain=Range(k + 1))
    if A is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        i = Symbol(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", Lamda[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol(Lamda[j](Cup[x[:k + 1]:s1_quote]({x_quote.cup_finiteset()})))

    return Equal(Card(Cup[j](A[j])), Sum[j](Card(A[j])))


@prove(proved=False)
def prove(Eq):
    from axiom import sets, algebra, discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n))
    Eq << apply(n, k)

    s1_quote = Eq[1].lhs
    Eq.s1_quote_definition = sets.imply.all.conditionset.apply(s1_quote)

    i = Eq[0].lhs.indices[0]
    Eq.x_abs_positive_s1 = algebra.all_et.imply.all.apply(Eq.s1_quote_definition)

    Eq.x_abs_sum_s1 = algebra.all_et.imply.all.apply(Eq.s1_quote_definition, 1)

    Eq.x_union_s1 = algebra.all_et.imply.all.apply(Eq.s1_quote_definition, 2)

    j = Symbol(domain=Range(k + 1))
    Eq << sets.eq.imply.eq.cup.apply(Eq[0], (i, 0, k + 1))

    Eq.x_quote_union = algebra.all_eq.cond.imply.all.subs.apply(Eq.x_union_s1, Eq[-1])

    Eq << Eq[0].apply(sets.eq.imply.eq.card)

    x_quote_abs = Eq[-1]
    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (i, 0, k + 1))

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << algebra.eq.le.imply.le.subs.apply(Eq[-2], Eq[-1])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_union.this.expr.apply(sets.eq.imply.eq.card)

    u = Eq[-1].lhs.arg
    Eq.SqueezeTheorem = sets.imply.le.cup.apply(u.expr, *u.limits)

    Eq << algebra.eq_piece.imply.ou.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-2], (i, Unequal(i, j)))

    Eq << sets.imply.ge.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.expr.apply(algebra.gt.ge.imply.gt.transit, Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq[-1]

    Eq.x_quote_definition = algebra.eq.imply.eq.lamda.apply(Eq[0], (i, 0, k + 1))

    Eq << Eq.x_union_s1.this.expr.apply(sets.eq.imply.eq.intersect, {n})

    Eq.nonoverlapping_s1_quote = Eq[-1].this.expr.apply(sets.is_empty.imply.all_is_empty.intersect)

    Eq.xi_complement_n = Eq.nonoverlapping_s1_quote.this.expr.apply(sets.intersect_is_empty.imply.eq.complement, reverse=True)

    A_quote = Symbol(Lamda[j](Eq[2].rhs.expr))
    Eq.A_quote_definition = A_quote.this.definition

    Eq.A_definition_simplified = Eq[2].this.rhs.subs(Eq.A_quote_definition[j].reversed)

    j_quote = Symbol(integer=True)
    Eq.nonoverlapping = All(Equal(A_quote[j_quote] & A_quote[j], A_quote[j].etype.emptySet), *((j_quote, Range(k + 1) - {j}),) + Eq.A_definition_simplified.rhs.limits, plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].this.expr.apply(sets.intersect_ne_empty.imply.any_el, simplify=None)

    Eq << Eq[-1].this.expr.subs(Eq.A_quote_definition[j])

    Eq << Eq[-1].this.expr.subs(Eq.A_quote_definition[j_quote])

    Eq << Eq[-1].this.expr.rhs.expr.arg.definition

    Eq << Eq[-1].this.expr.apply(sets.eq.imply.supset)

    Eq << Eq[-1].this.expr.apply(sets.supset_cup.imply.all_supset)

    Eq << Eq[-1].this.expr.subs(Eq[-1].expr.variable, Eq[-1].variable)

    Eq << Eq[-1].this.expr.apply(sets.el_cup.imply.any_el)

    Eq << Eq[-1].this.expr.subs(Eq.x_quote_definition)

    Eq << Eq[-1].this.expr.apply(algebra.eq_piece.imply.ou)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.all_et.given.et.all)

    return
    Eq << algebra.et.given.conds.apply(Eq[-1])
    return
    Eq <<= ~Eq[-1], ~Eq[-2]
    Eq << algebra.any_et.imply.any.limits_delete.apply(Eq[-2])
    Eq << algebra.any_et.imply.any.split.apply(Eq[-2], simplify=False, index=1).apply(sets.eq.imply.eq.intersect, {n})
    Eq << Eq[-1].subs(Eq.nonoverlapping_s1_quote)
    Eq << Eq[-2].this.expr.apply(sets.eq.imply.eq.complement, {n})
    Eq << Eq[-1].limits_subs(j_quote, i)
    Eq << Eq[-1].subs(Eq.xi_complement_n.subs(i, j)).subs(Eq.xi_complement_n)
    _i = i.copy(domain=Range(k + 1) - {j})
    Eq << Eq[-1].limits_subs(i, _i)
    Eq << Eq.x_union_s1.function.lhs.this.bisect({_i, j})
    Eq << Eq[-1].subs(Eq[-2].reversed)
    Eq << sets.imply.le.cup.apply(*Eq[-1].rhs.args)
    Eq << Eq[-2].apply(algebra.eq.imply.eq.abs)
    Eq << Eq[-1].subs(Eq.x_union_s1) + Eq[-2]
    Eq << Eq[-1] + Eq.x_abs_sum_s1
    Eq <<= Eq[-1] & Eq.x_abs_positive_s1.subs(i, j)
    Eq << discrete.combinatorics.permutation.is_nonempty.s1.apply(n, k=k + 1)
    Eq << Eq[-1].subs(Eq[1].reversed)
    Eq <<= Eq[-1] & Eq[-3]
    Eq << Eq.nonoverlapping.apply(sets.eq.imply.eq.cup, Eq.nonoverlapping.limits[1])
    Eq << Eq[-1].this.expr.lhs.astype(Intersection)
    Eq << Eq.A_definition_simplified.subs(j, j_quote)
    Eq << Eq[-2].subs(Eq[-1].reversed, Eq.A_definition_simplified.reversed)
    Eq << sets.all_is_empty.imply.eq.nonoverlapping.setlimit.apply(Eq[-1])
    Eq << Eq[-1].this.lhs.arg.limits_subs(j_quote, j)
    Eq << Eq[-1].this.rhs.limits_subs(j_quote, j)


if __name__ == '__main__':
    run()

# created on 2020-08-11
