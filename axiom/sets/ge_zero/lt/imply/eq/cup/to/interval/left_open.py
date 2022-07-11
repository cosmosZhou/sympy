from util import *


@apply
def apply(is_nonnegative, lt, k=None):
    a = is_nonnegative.of(Expr >= 0)
    S[a], b = lt.of(Less)

    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a >= 0, a < b, k)

    Eq << algebra.lt.imply.eq.min.apply(Eq[1])

    Eq << algebra.eq.ge.imply.ge.add.apply(Eq[-1], Eq[0])

    Eq << sets.ge_zero.imply.eq.cup.to.interval.left_open.apply(Eq[-1], k)

    Eq << Eq[-1].this.rhs.subs(Eq[-3])

    Eq << sets.cup.to.union.split.apply(Cup[k:b](Eq[-1].lhs.expr), cond=Range(a))

    Eq << Eq[-1].subs(Eq[-2])

    Eq.b_is_nonnegative = algebra.ge.lt.imply.ge.relax.apply(Eq[0], Eq[1])

    Eq << sets.ge_zero.imply.eq.cup.to.interval.left_open.apply(Eq.b_is_nonnegative, k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_a = Eq[-1].rhs.args[0]
    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], interval_a)

    Eq << algebra.ge.imply.eq.min.apply(Eq.b_is_nonnegative)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.ge.imply.eq.max.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1]).reversed

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << sets.intersect_ne_empty.imply.any_el.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(sets.el_cup.imply.any_el)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.imply.et)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.et, slice(0, 3, 2))

    Eq << Eq[-1].this.find(GreaterEqual).apply(algebra.ge.imply.gt.relax, plus=True, ret=0)

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt.imply.eq.min)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.cond.imply.cond.subs)

    Eq << algebra.cond.any.imply.any_et.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.ge.ge.imply.ge.transit, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.ge.imply.eq.max)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.expr.args[0].apply(sets.interval_ne_empty.imply.gt)

    Eq << sets.intersect_is_empty.eq_complement.imply.eq.apply(Eq.is_empty, Eq.eq_complement)


if __name__ == '__main__':
    run()
# created on 2018-09-17
