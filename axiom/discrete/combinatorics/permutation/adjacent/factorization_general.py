from util import *

from axiom.sets.imply.eq.swap import swap


@apply
def apply(given):
    from axiom.sets.eq.given.eq.set_comprehension import of_set_comprehension
    set_comprehension_abs, n = given.of(Equal)
    set_comprehension = set_comprehension_abs.of(Abs)
    a = of_set_comprehension(set_comprehension)

    assert a.shape == (n,)

    i = Symbol.i(integer=True)

    p = Symbol.p(shape=(oo,), **a.dtype.dict)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), set_comprehension)))

    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)

    k = Symbol.k(integer=True)

    d = Symbol.d(Lamda[i:n](i) @ MatProduct[i:n](Swap(n, i, b[i])))
    return All[p[:n]:P](Any[b[:n]](Equal(p[:n], Lamda[k:n](a[d[k]]))))


@prove(proved=False)
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(domain=Range(2, oo), given=False)

    a = Symbol.a(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Equal(Abs(a[:n].set_comprehension()), n))

    i = Symbol.i(integer=True)
    p = Eq[3].variable.base
    b = Eq[3].function.variable.base

    Eq.hypothesis = Eq[3].subs(Eq[1]).copy(plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.this.function.function.rhs.function.indices[0].definition

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.matrix)

    return
    Eq.initial_doit = Eq[-1].doit(deep=True)

    d0 = Symbol.d0(Eq.initial_doit.rhs[0].indices[0])

    Eq << d0.this.definition

    Eq.initial_doit = Eq.initial_doit.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.args[-1][1].simplify()

    Eq << Eq[-1].this.rhs.args[-1][0].simplify()

    Eq << Eq[-1].this.rhs.args[1].astype(Lamda)

    Eq << Eq[-1].this.rhs.args[1].astype(Matrix)

    Eq << Eq[-1].this.rhs.args[1][0, 0].simplify()

    Eq << Eq[-1].this.rhs.args[1][0, 1].simplify()

    Eq << Eq[-1].this.rhs.args[1][1, 0].simplify()

    Eq << Eq[-1].this.rhs.args[1][1, 1].simplify()

    Eq << Eq[-1].this.rhs.args[1][1, 1].simplify()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq.initial_doit = Eq.initial_doit.subs(Eq[-1])

    d1 = Symbol.d1(Eq.initial_doit.rhs[1].indices[0])
    Eq << d1.this.definition

    Eq.initial_doit = Eq.initial_doit.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.rhs.args[1].astype(Lamda)

    Eq << Eq[-1].this.rhs.args[1].astype(Matrix)

    Eq << Eq[-1].this.rhs.args[1][0, 0].simplify()

    Eq << Eq[-1].this.rhs.args[1][0, 1].simplify()

    Eq << Eq[-1].this.rhs.args[1][1, 0].simplify()

    Eq << Eq[-1].this.rhs.args[1][1, 1].simplify()

    Eq << Eq[-1].this.rhs.args[1][1, 1].simplify()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq.initial_doit.subs(Eq[-1])

    p0 = Eq[-1].variable
    Eq << Eq[-1].subs(b[:2], Matrix((0, KroneckerDelta(p0, a[0]))))

    Eq << algebra.imply.all.limits_assert.apply(Eq[-1].limits)

    Eq << Eq[-1].this.function.apply(sets.eq.imply.eq.split.finiteset.indexed)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq.induct_swap = Eq.induct.apply(sets.eq.given.eq.swap, n, b[n])

    Eq << discrete.combinatorics.permutation.any.apply(a[:n + 1])
    Eq << Eq[-1].this.limits[0][1].definition

    Eq << Eq[-1].this.function.limits_subs(Eq[-1].function.variable, b[n])

    Eq.p_swap = swap[n, b[n]](p[:n + 1]).this.definition

    Eq.a_swap = swap[n, b[n]](Eq.induct.rhs).this.definition

    Eq.d_induction_definition = Eq.induct.function.function.rhs.function.indices[0].base.this.definition

    Eq << discrete.matrix.elementary.swap.identity.apply(Eq.d_induction_definition.lhs, left=False)

    i, j = Eq[-1].rhs.args[1].indices
    Eq.d_swap = Eq[-1].subs(i, n).subs(j, b[n])

    Eq << Eq.d_induction_definition.rhs.args[1].this.bisect(slice(-1))

    Eq << axiom.discrete.matrix.elementary.swap.concatenate_product.apply(n, n, b)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.d_induction_definition.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].bisect(slice(-1))

    Eq << MatMul(*Eq[-1].rhs.args[:2]).this.expand()

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)

    Eq << Eq[-3].subs(Eq[-1])

    Eq.deduction = Eq[-1] @ Eq[-1].rhs.args[1]

    d_quote = Symbol.d_quote(Eq.deduction.lhs)

    Eq.d_quote_definition = d_quote.this.definition

    Eq << Eq.d_swap.this.rhs.args[1].definition - Eq.d_quote_definition + Eq.d_quote_definition.lhs

    Eq << algebra.eq.imply.eq.getitem.apply(Eq[-1], a, i=Eq[-1].lhs.variable, simplify=None)

    return
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq.a_swap, Eq[-1])

    Eq << Eq.induct_swap.apply(algebra.eq.eq.given.eq.transit, Eq[-1])

    Eq.deduction = Eq.deduction.subs(Eq.d_quote_definition.reversed)

    Eq << Eq.d_quote_definition.lhs[n].this.definition

    Eq << Eq[-1].this.rhs.args[1].function.astype(KroneckerDelta)

    Eq << Eq[-1].this.rhs.expand()
    return

    Eq << Eq[-1].subs(Eq.any_n)

    Eq << Eq[-1].this.function().function.rhs.simplify()
    Eq.any_n_plausible = Eq[-1].this.function.exists((Eq[-1].function.variable,))

    Eq << discrete.matrix.elementary.swap.invariant.permutation.apply(n + 1, left=False)

    i, j = Eq[-1].function.lhs.args[1].indices
    Eq << Eq[-1].subs(Eq[-1].function.lhs.args[1].this.definition)

    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.any_n_plausible.variable).subs(Eq.p_quote_definition.reversed)

    Eq << Eq[-1].subs(Eq[-1].function.rhs.this.definition)

    Eq << Eq.any_n_plausible.apply(discrete.combinatorics.permutation.pop_back, Eq[-1])

#     Eq << Eq.hypothesis.subs(Eq.hypothesis.variable, p_quote[:n])

    Eq << Eq[-1].subs(Eq[-2].reversed)

    Eq << Eq.p_quote_definition.lhs.this.bisect(slice(-1))

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].subs(Eq.any_n_plausible)

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
