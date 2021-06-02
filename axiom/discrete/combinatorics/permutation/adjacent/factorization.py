from util import *


@apply
def apply(n):
    i = Symbol.i(integer=True)

    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)

    P = Symbol.P(conditionset(p[:n], Equal(p[:n].set_comprehension(), Range(0, n))))

    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)

    return ForAll[p[:n]:P](Exists[b[:n]](Equal(p[:n], Lamda[i:n](i) @ MatProduct[i:n](Swap(n, i, b[i])))))


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra
    n = Symbol.n(domain=Range(2, oo), given=False)

    Eq << apply(n)

    b = Eq[1].function.variable.base

    Eq.hypothesis = Eq[1].subs(Eq[0]).copy(plausible=True)

    Eq.initial = Eq.hypothesis.subs(n, 2)

    Eq << Eq.initial.doit(deep=True)

    p0 = Eq[-1].variable
    Eq << Eq[-1].this.function.apply(algebra.any.given.any.subs, b[:2], Matrix((0, KroneckerDelta(p0, 0))))

    Eq << Eq[-1].this.function.rhs.expand()

    Eq << Eq[-1].this.function.rhs[0].simplify()

    Eq.equation = Eq[-1].this.function.rhs[1].simplify()

    Eq.limits_assertion = algebra.imply.all.limits_assert.apply(Eq.equation.limits)

    Eq << Eq.limits_assertion.this.function.apply(sets.eq.imply.eq.split.finiteset.add)

    Eq.p1_equality = Eq[-1].this.function - p0

    Eq <<= Eq.equation & Eq.p1_equality

    Eq << Eq[-1].this.function.apply(algebra.et.given.et.subs.eq, index=1)

    Eq << algebra.all_et.given.all.apply(Eq[-1])

    Eq << Eq[-1].this.function.apply(algebra.eq.given.et.split.matrix)

    Eq.premier, Eq.second = algebra.all_et.given.all.apply(Eq[-1])

    Eq << Eq.limits_assertion.this.function.apply(sets.eq.imply.et.split.finiteset)

    Eq << algebra.all_et.imply.all.apply(Eq[-1])

    Eq << Eq[-2].this.function.apply(sets.contains.imply.eq.kronecker_delta.zero).reversed

    Eq << -(Eq.premier - 1)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.function.function.rhs.args[1].this.split(Slice[-1:])

    Eq << discrete.matrix.elementary.swap.concatenate_product.apply(n, n, b)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.induct.subs(Eq[-1])

    Eq << Eq[-1].this.function.function.rhs.args[0].split(Slice[-1:])

    Eq << MatMul(*Eq[-1].function.function.rhs.args[:2]).this.expand()

    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)

    Eq << Eq[-3].subs(Eq[-1])

    Eq.deduction = Eq[-1].this.function.function @ Eq[-1].function.function.rhs.args[1]

    Eq << discrete.combinatorics.permutation.any.basic.apply(n + 1)

    Eq << Eq[-1].this.function.limits_subs(Eq[-1].function.variable, b[n])

    Eq.any_n = Eq[-1].this.limits[0][1].definition

    p_quote = Symbol.p_quote(Eq.deduction.function.function.lhs)

    Eq.p_quote_definition = p_quote.this.definition

    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)

    Eq << Eq.p_quote_definition.lhs[n].this.definition

    Eq << Eq[-1].this.rhs.args[1].function.astype(KroneckerDelta)

    Eq << Eq[-1].this.rhs.expand()

    Eq << algebra.all_any_eq.cond.imply.all_any.subs.apply(Eq.any_n, Eq[-1])

    Eq << Eq[-1].this.function().function.rhs.simplify()

    Eq.any_n_plausible = Eq[-1].this.function.apply(sets.any.imply.any.limits.relax, wrt=Eq[-1].function.variable)

    Eq << discrete.matrix.elementary.swap.invariant.permutation.basic.apply(n + 1, left=False)

    i, j = Eq[-1].find(Indexed).indices
    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.any_n_plausible.variable).subs(Eq.p_quote_definition.reversed)

    Eq << Eq[-1].this.function.rhs.definition

    Eq << Eq[-1].this.limits[0][1].definition

    Eq <<= Eq.any_n_plausible & Eq[-1]

    Eq << Eq[-1].this.function.apply(algebra.cond.any.imply.any_et)

    Eq << Eq[-1].this.function.function.apply(discrete.combinatorics.permutation.pop_back.interval)

    Eq << algebra.all.imply.ou.subs.apply(Eq.hypothesis, Eq.hypothesis.variable, p_quote[:n])

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.function.apply(algebra.any.ou.imply.cond, simplify=None)

    Eq << Eq.p_quote_definition.lhs.this.split(Slice[-1:])

    Eq << algebra.cond.all_any.imply.all_any_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.subs, swap=True)

    Eq <<= Eq[-1] & Eq.any_n_plausible

    Eq << Eq[-1].this.function.apply(algebra.any.any.imply.any_et, simplify=None)

    Eq << Eq[-1].this.function.function.apply(algebra.eq.eq.imply.eq.subs, swap=True)

    Eq << Eq.induct.induct()

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=2)

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
