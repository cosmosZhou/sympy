from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(-1, 1, left_open=True, right_open=True)
    assert domain_y in Interval(-1, 1, left_open=True, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(-1, 1, left_open=True, right_open=True)), Element(y, Interval(-1, 1, left_open=True, right_open=True)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=y > 0)

    Eq <<= algebra.cond.given.et.infer.split.apply(Eq[-2], cond=x > 0), algebra.cond.given.et.infer.split.apply(Eq[-1], cond=x > 0)

    Eq.gt_gt, Eq.le_gt, Eq.gt_le, Eq.le_le = Eq[-4].this.apply(algebra.infer.flatten), Eq[-3].this.apply(algebra.infer.flatten), Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq << sets.el.imply.sqrt_gt_zero.apply(Eq[2])

    Eq << algebra.cond.imply.infer.et.apply(Eq[-1], cond=x <= 0)

    Eq.x_is_nonpositive = Eq[-1].this.rhs.apply(algebra.le_zero.gt_zero.imply.le_zero)

    Eq << sets.el.imply.sqrt_gt_zero.apply(Eq[1])

    Eq << algebra.cond.imply.infer.et.apply(Eq[-1], cond=y > 0)

    Eq << Eq[-1].this.rhs.apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq.x_is_nonpositive, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.le.gt.imply.gt.transit)

    Eq << Eq.gt_le.this.lhs.apply(algebra.gt.le.imply.gt.transit)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ge.relax)

    Eq << algebra.cond.given.cond.subs.bool.apply(Eq[-1], cond=Eq[0], invert=True)

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[1], cond=x > 0), algebra.cond.imply.infer.et.apply(Eq[2], cond=y > 0)

    Eq <<= Eq[-2].this.rhs.apply(sets.gt.el.imply.el.intersect), Eq[-1].this.rhs.apply(sets.gt.el.imply.el.intersect)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[-1], Eq[-2])

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(sets.lt.el.el.imply.gt.sqrt.open.positive)

    Eq <<= algebra.cond.imply.infer.et.apply(Eq[1], cond=x <= 0), algebra.cond.imply.infer.et.apply(Eq[2], cond=y <= 0)

    Eq <<= Eq[-2].this.rhs.apply(sets.le.el.imply.el.intersect), Eq[-1].this.rhs.apply(sets.le.el.imply.el.intersect)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[-1], Eq[-2])

    Eq << algebra.cond.imply.infer.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(sets.lt.el.el.imply.gt.sqrt.open.nonpositive)


if __name__ == '__main__':
    run()

from . import positive
from . import nonpositive
from . import nonnegative
# created on 2020-11-29
