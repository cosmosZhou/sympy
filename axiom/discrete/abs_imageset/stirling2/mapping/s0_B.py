from util import *


@apply
def apply(n, k, s0=None, B=None):
    from sympy.functions.combinatorial.numbers import Stirling
    if s0 is None:
        x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
        s0 = Symbol(Cup[x[:k]:Stirling.conditionset(n, k, x)](x[:k].cup_finiteset().set))
    if B is None:
        e = Symbol(**s0.etype.dict)
        assert e.is_extended_real
        B = Symbol(Cup[e:s0]({e | {n.set}}))

        assert B.definition.variable.is_extended_real
    return Equal(Card(s0), Card(B))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n, k = Symbol(integer=True, positive=True, given=True)
    Eq << apply(n, k)

    s0 = Eq[0].lhs
    s0_quote = Symbol('s_quote_0', conditionset(Eq[0].rhs.variable, Eq[0].rhs.limits[0][1]))
    Eq << s0_quote.this.definition

    Eq.s0_definition = imageset(Eq[0].rhs.variable, Eq[0].rhs.expr.arg, s0_quote).this.subs(Eq[-1]).subs(Eq[0].reversed).reversed

    e = Symbol(etype=dtype.integer.set)
    Eq << sets.imply.all.baseset.apply(s0_quote)

    * _, Eq.x_union_s0 = algebra.all_et.imply.et.all.apply(Eq[-1])

    i = Symbol(integer=True)
    x = Eq[0].rhs.variable.base
    j = Symbol(domain=Range(k + 1))
    B = Eq[1].lhs
    Eq.plausible_notcontains = All(NotElement({n}, e), (e, s0), plausible=True)

    Eq << Eq.plausible_notcontains.this.limits[0][1].subs(Eq.s0_definition)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(sets.el_cup.imply.any_el)

    Eq << algebra.all.any.imply.any_et.apply(Eq.x_union_s0, Eq[-1].reversed, simplify=None)

    Eq << Eq[-1].this.expr.apply(sets.eq.eq.imply.eq.union)

    Eq << Eq[-1].this().expr.lhs.simplify()

    Eq << algebra.all_eq.any.imply.any.subs.apply(Eq.x_union_s0, Eq[-1])

    Eq << Eq.plausible_notcontains.this.expr.apply(sets.notin.imply.is_empty.intersect)

    Eq.all_s0_equality = Eq[-1].this.expr.apply(sets.intersect_is_empty.imply.eq.complement)

    x_hat = Symbol(r"\hat{x}", Lamda[i](Piecewise((x[i] - {n} , Equal(i, j)), (x[i], True))))
    Eq.x_hat_definition = x_hat[i].this.definition

    Eq << algebra.eq_piece.imply.ou.apply(Eq.x_hat_definition)

    Eq.B_assertion = sets.imply.all_any_eq.split.imageset.apply(B)

    Eq << Eq.B_assertion.this.expr.expr.apply(sets.eq.imply.eq.complement, {n.set})

    Eq << algebra.cond.all.imply.all_et.apply(Eq.all_s0_equality, Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.all.any.imply.any_et)

    Eq.all_B_contains = Eq[-1].this.expr.expr.apply(algebra.eq.eq.imply.eq.subs, swap=True).limits_subs(Eq[-1].variable, Eq.all_s0_equality.variable)

    Eq.all_s0_contains = sets.imply.all_el.split.imageset.apply(B)

    Eq << Eq.B_assertion.this.expr.expr.apply(sets.eq.imply.eq.intersect, {n.set})

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << Eq[-1].limits_subs(Eq.B_assertion.variable, Eq.B_assertion.expr.variable)

    Eq.all_B_equality = Eq[-1].this.expr.apply(sets.eq.imply.eq.union, Eq[-1].variable)

    Eq << sets.all_el.all_el.all_eq.all_eq.imply.eq.apply(Eq.all_s0_contains,
                                                                                  Eq.all_B_contains,
                                                                                  Eq.all_s0_equality,
                                                                                  Eq.all_B_equality)


if __name__ == '__main__':
    run()

# created on 2020-08-14
