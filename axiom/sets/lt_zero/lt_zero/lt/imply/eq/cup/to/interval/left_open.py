from util import *


@apply
def apply(a_is_negative, b_is_negative, lt, k=None):
    a = a_is_negative.of(Expr < 0)
    b = b_is_negative.of(Expr < 0)
    S[a], S[b] = lt.of(Less)
    assert a.is_integer and b.is_integer
    if k is None:
        k = a.generate_var(b.free_symbols, integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True, given=True)
    k = Symbol(integer=True)
    Eq << apply(a < 0, b < 0, a < b, k)

    Eq << sets.cup.to.union.split.apply(Cup[k:a:0](Eq[-1].lhs.expr), cond=Range(b, 0))

    Eq.min_b0 = algebra.lt.imply.eq.min.apply(Eq[1])

    Eq << algebra.lt.imply.eq.max.apply(Eq[2])

    Eq <<= Eq[-2].rhs.args[0].this.subs(Eq.min_b0), Eq[-2].rhs.args[1].this.subs(Eq[-1])

    Eq << sets.lt_zero.imply.eq.cup.to.interval.left_open.apply(Eq[1], k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[4].subs(Eq[-1], Eq[-4]).reversed

    Eq << sets.lt_zero.imply.eq.cup.to.interval.left_open.apply(Eq[0], k)

    Eq << Eq[-2].subs(Eq[-1])

    interval_b = Eq[-1].lhs.args[0]
    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], interval_b)

    Eq << algebra.lt.imply.eq.max.apply(Eq[0])

    Eq.eq_complement = Eq[-2].subs(Eq[-1], Eq.min_b0)

    Eq.is_empty = Equal(Intersection(*Eq.eq_complement.lhs.args), Eq.eq_complement.rhs.etype.emptySet, plausible=True)

    Eq << ~Eq.is_empty

    Eq << sets.intersect_ne_empty.imply.any_el.apply(Eq[-1], simplify=None, index=1)

    Eq << Eq[-1].this.expr.apply(sets.el_cup.imply.any_el)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.el_range.imply.et)

    Eq << Eq[-1].this.expr.apply(algebra.et.imply.cond, slice(0, 2))

    Eq << algebra.cond.any.imply.any_et.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.lt.lt.imply.lt.transit, ret=1)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.lt.imply.le.strengthen.plus)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.le.imply.eq.min)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.expr.args[1].apply(algebra.lt.imply.eq.max, ret=0)

    Eq << Eq[-1].this.expr.args[:2].apply(algebra.eq.cond.imply.cond.subs)

    Eq << Eq[-1].this.expr.args[0].apply(sets.interval_ne_empty.imply.gt)

    Eq << Eq[-1].this.expr.args[0].apply(algebra.gt.imply.ge.strengthen)

    Eq << sets.eq.eq.imply.eq.union.apply(Eq.eq_complement, Eq.is_empty)





if __name__ == '__main__':
    run()
# created on 2018-10-15
# updated on 2021-11-23