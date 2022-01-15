from util import *


@apply
def apply(n, k):
    from sympy.functions.combinatorial.numbers import Stirling
    assert k < n
    return Equal(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(1, n))
    Eq << apply(n, k)

    Eq.stirling2 = Eq[0].lhs.this.apply(discrete.stirling2.to.abs)

    Eq.stirling0 = Eq[0].rhs.args[1].this.apply(discrete.stirling2.to.abs)

    Eq.stirling1 = Eq[0].rhs.args[0].args[1].this.apply(discrete.stirling2.to.abs)

    s2 = Symbol(Eq.stirling2.rhs.arg)
    Eq << s2.this.definition

    Eq.stirling2 = Eq.stirling2.subs(Eq[-1].reversed)

    s0 = Symbol(Eq.stirling0.rhs.arg)
    Eq << s0.this.definition

    Eq.stirling0 = Eq.stirling0.subs(Eq[-1].reversed)

    s1 = Symbol(Eq.stirling1.rhs.arg)
    Eq << s1.this.definition

    Eq.stirling1 = Eq.stirling1.subs(Eq[-1].reversed)

    e = Symbol(etype=dtype.integer.set)
    Eq << sets.imply.eq.union.apply(s2, conditionset(e, Element({n}, e), s2))


    Eq.s2_abs = Eq[-1].apply(sets.eq.imply.eq.card)

    Eq.s2_abs_plausible = Eq[0].subs(Eq.stirling2, Eq.stirling0, Eq.stirling1)

    Eq << discrete.condset.to.cup.stirling2.mapping.s2_A.apply(n, k, s2)

    A = Eq[-1].rhs.expr.base
    Eq << discrete.condset.stirling2.mapping.s2_B.apply(n, k, s2)

    B = Eq[-1].rhs
    Eq.s2_abs = Eq.s2_abs.subs(Eq[-1], Eq[-2])

    Eq << discrete.abs_imageset.stirling2.mapping.s0_B.apply(n, k, s0, B)

    Eq << Eq.s2_abs.subs(Eq[-1].reversed)

    Eq.A_union_abs = Eq.s2_abs_plausible.subs(Eq[-1]) - Card(s0)

    Eq << discrete.abs_cup.to.sum.stirling2.nonoverlapping.A.apply(n, k, A)

    Eq << Eq.A_union_abs.subs(Eq[-1])

    Eq << discrete.abs_condset.stirling2.mapping.s1_Aj.apply(n, k, s1, A).reversed

    Eq << Eq[-1].apply(algebra.eq.imply.eq.sum, *Eq[-2].lhs.limits)


if __name__ == '__main__':
    run()

# created on 2020-10-06
