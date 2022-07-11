from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(0, oo, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, right_open=True)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_interval.imply.ge), Eq[-1].this.rhs.apply(algebra.any.given.cond.subs, k, Floor(x))

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.imply.any_et.limits.unleash, simplify=None), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.expr.args[0].apply(sets.el_range.imply.ge), algebra.infer.given.cond.apply(Eq[-2]), Eq[-1].this.rhs.apply(sets.el_range.given.et)

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.imply.ge)

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.ge.ge.imply.ge.transit), sets.el_interval.given.et.apply(Eq[-2])

    Eq << Eq[-3].this.lhs.apply(sets.ge_zero.imply.is_nonnegative, simplify=None)

    Eq << algebra.imply.lt.floor.apply(x)

    Eq << algebra.imply.ge.floor.apply(x)


if __name__ == '__main__':
    run()
# created on 2021-02-14
