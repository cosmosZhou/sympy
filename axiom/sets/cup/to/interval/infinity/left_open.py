from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(0, oo, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, left_open=True)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.imply.any_el), Eq[-1].this.rhs.apply(sets.el_cup.given.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_interval.imply.gt), Eq[-1].this.rhs.apply(algebra.any.given.cond.subs, k, Ceiling(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.imply.any_et.limits.unleash, simplify=None), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.expr.args[0].apply(sets.el_range.imply.ge), algebra.infer.given.cond.apply(Eq[-2]), Eq[-1].this.rhs.apply(sets.el_range.given.et)

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.gt.ge.imply.gt.transit), sets.el_interval.given.et.apply(Eq[-2]), Eq[-1].this.rhs.apply(algebra.ge.transport, lhs=0)

    Eq << Eq[-4].this.lhs.apply(sets.gt_zero.imply.is_positive, simplify=None)

    Eq << algebra.imply.gt.ceiling.apply(x)

    Eq << algebra.imply.le.ceiling.apply(x)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.imply.gt_zero.ceiling)
    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ge.strengthen)



if __name__ == '__main__':
    run()
# created on 2021-02-13
