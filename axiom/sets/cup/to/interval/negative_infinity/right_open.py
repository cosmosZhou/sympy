from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(-oo, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, right_open=True)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_interval.imply.lt), Eq[-1].this.rhs.apply(algebra.any.given.cond.subs, k, -Floor(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.imply.any_et.limits.unleash, simplify=None), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.expr.args[0].apply(sets.el_range.imply.le), Eq[-2].this.rhs.apply(sets.el_range.given.et), algebra.infer.given.cond.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.le.lt.imply.lt.add), Eq[-2].this.rhs.apply(algebra.ge.transport, lhs=0), sets.el_interval.given.et.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(sets.lt_zero.imply.is_negative, simplify=None)

    Eq << algebra.imply.ge.floor.apply(x)

    Eq << algebra.imply.lt.floor.apply(x)

    Eq << -Eq[-3].this.rhs

    Eq << Eq[-1].this.rhs.apply(algebra.le.given.lt.one)

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.imply.lt)
    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.imply.floor_lt_zero)


if __name__ == '__main__':
    run()
# created on 2021-02-17
