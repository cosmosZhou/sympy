from util import *


@apply
def apply(n, k, A=None):
    from sympy.functions.combinatorial.numbers import Stirling
    assert k < n
    j = Symbol.j(domain=Range(0, k + 1))
    if A is None:
        x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
        i = Symbol.i(integer=True)
        s1_quote = Symbol("s'_1", Stirling.conditionset(n, k + 1, x))
        x_quote = Symbol("x'", Lamda[i:k + 1](Piecewise(({n} | x[i], Equal(i, j)), (x[i], True))))
        A = Symbol.A(Lamda[j](Cup[x[:k + 1]:s1_quote]({x_quote.set_comprehension()})))

    return Equal(abs(Cup[j](A[j])), Sum[j](abs(A[j])))


@prove(surmountable=False)
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(domain=Range(1, n))

    Eq << apply(n, k)
    s1_quote = Eq[1].lhs

    Eq.s1_quote_definition = sets.imply.all.conditionset.apply(s1_quote)

    i = Eq[0].lhs.indices[0]

    Eq.x_abs_positive_s1, Eq.x_abs_sum_s1, Eq.x_union_s1 = algebra.all_et.imply.all.apply(Eq.s1_quote_definition)

    j = Symbol.j(domain=Range(0, k + 1))

    Eq << sets.eq.imply.eq.cup.apply(Eq[0], (i, 0, k + 1))

    Eq.x_quote_union = algebra.all_eq.cond.imply.all.subs.apply(Eq.x_union_s1, Eq[-1])

    Eq << Eq[0].apply(algebra.eq.imply.eq.abs)
    x_quote_abs = Eq[-1]

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, (i, 0, k + 1))

    Eq << sets.imply.le.union.apply(*Eq[-1].rhs.args[1].arg.args)

    Eq << algebra.eq.le.imply.le.subs.apply(Eq[-2], Eq[-1])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.x_abs_sum_s1, Eq[-1])

    Eq << Eq.x_quote_union.this.function.apply(algebra.eq.imply.eq.abs)

    u = Eq[-1].lhs.arg
    Eq.SqueezeTheorem = sets.imply.le.cup.apply(u.function, *u.limits)

    Eq << algebra.eq_piecewise.imply.ou.apply(x_quote_abs)

    Eq << Eq[-1].subs(i, j)

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-2], (i, Unequal(i, j)))

    Eq << sets.imply.ge.apply(*Eq[-2].rhs.arg.args[::-1])

    Eq << Eq.x_abs_positive_s1.limits_subs(i, j).this.function.apply(algebra.gt.ge.imply.gt.transit, Eq[-1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq <<= Eq.x_quote_union & Eq.SqueezeTheorem & Eq[-1]

    Eq.x_quote_definition = algebra.eq.imply.eq.lamda.apply(Eq[0], (i, 0, k + 1))

    Eq << Eq.x_union_s1.this.function.apply(sets.eq.imply.eq.intersection, {n})

    Eq.nonoverlapping_s1_quote = Eq[-1].this.function.apply(sets.is_emptyset.imply.all_is_emptyset.intersection)

    Eq.xi_complement_n = Eq.nonoverlapping_s1_quote.this.function.apply(sets.is_emptyset.imply.eq.complement, reverse=True)

    A_quote = Symbol.A_quote(Lamda[j](Eq[2].rhs.function))

    Eq.A_quote_definition = A_quote.this.definition

    Eq.A_definition_simplified = Eq[2].this.rhs.subs(Eq.A_quote_definition[j].reversed)

    j_quote = Symbol.j_quote(integer=True)

    Eq.nonoverlapping = ForAll(Equal(A_quote[j_quote] & A_quote[j], A_quote[j].etype.emptySet), *((j_quote, Range(0, k + 1) // {j}),) + Eq.A_definition_simplified.rhs.limits, plausible=True)

    Eq << ~Eq.nonoverlapping

    Eq << Eq[-1].this.function.apply(sets.is_nonemptyset.imply.any_contains.st.intersection, simplify=None)

    Eq << Eq[-1].this.function.subs(Eq.A_quote_definition[j])

    Eq << Eq[-1].this.function.subs(Eq.A_quote_definition[j_quote])

    Eq << Eq[-1].this.function.rhs.function.arg.definition

    Eq << Eq[-1].this.function.apply(sets.eq.imply.supset)

    Eq << Eq[-1].this.function.apply(sets.supset.imply.all_supset.split.cup)

    Eq << Eq[-1].this.function.subs(Eq[-1].function.variable, Eq[-1].variable)

    Eq << Eq[-1].this.function.apply(sets.contains.imply.any_contains.st.cup)

    Eq << Eq[-1].this.function.subs(Eq.x_quote_definition)

    Eq << Eq[-1].this.function.apply(algebra.eq_piecewise.imply.ou)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.function.apply(algebra.all_et.given.all)
    return
    Eq << algebra.et.given.conds.apply(Eq[-1])
    return
    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << algebra.any_et.imply.any.limits_delete.apply(Eq[-2])

    Eq << algebra.any_et.imply.any.split.apply(Eq[-2], simplify=False, index=1).apply(sets.eq.imply.eq.intersection, {n})

    Eq << Eq[-1].subs(Eq.nonoverlapping_s1_quote)

    Eq << Eq[-2].this.function.apply(sets.eq.imply.eq.complement, {n})

    Eq << Eq[-1].limits_subs(j_quote, i)

    Eq << Eq[-1].subs(Eq.xi_complement_n.subs(i, j)).subs(Eq.xi_complement_n)

    _i = i.copy(domain=Range(0, k + 1) // {j})
    Eq << Eq[-1].limits_subs(i, _i)

    Eq << Eq.x_union_s1.function.lhs.this.bisect({_i, j})

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << sets.imply.le.cup.apply(*Eq[-1].rhs.args)

    Eq << Eq[-2].apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1].subs(Eq.x_union_s1) + Eq[-2]

    Eq << Eq[-1] + Eq.x_abs_sum_s1

    Eq <<= Eq[-1] & Eq.x_abs_positive_s1.subs(i, j)

    Eq << discrete.combinatorics.permutation.is_nonemptyset.s1.apply(n, k=k + 1)

    Eq << Eq[-1].subs(Eq[1].reversed)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq.nonoverlapping.apply(sets.eq.imply.eq.cup, Eq.nonoverlapping.limits[1])

    Eq << Eq[-1].this.function.lhs.astype(Intersection)

    Eq << Eq.A_definition_simplified.subs(j, j_quote)

    Eq << Eq[-2].subs(Eq[-1].reversed, Eq.A_definition_simplified.reversed)

    Eq << sets.all_is_emptyset.imply.eq.nonoverlapping.setlimit.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.arg.limits_subs(j_quote, j)

    Eq << Eq[-1].this.rhs.limits_subs(j_quote, j)


if __name__ == '__main__':
    run()

