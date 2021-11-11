from util import *


@apply
def apply(given, right_open=True):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    return Equal(interval, Interval(a, x, left_open=interval.left_open, right_open=right_open) | Interval(x, b, left_open=not right_open, right_open=interval.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), right_open=False)

    Eq << sets.eq.given.et.infer.apply(Eq[1], t)

    Eq <<= Eq[-2].this.rhs.apply(sets.el.given.ou.split.union), Eq[-1].this.lhs.apply(sets.el.imply.ou.split.union)

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.et.split.interval), Eq[-1].this.rhs.apply(sets.el.given.et.split.interval)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.interval), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.interval)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.interval), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.interval)

    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq[-1])

    Eq <<= algebra.infer.given.infer.split.et.apply(Eq[-2], 1), algebra.infer.given.infer.split.et.apply(Eq[-1], 0)

    Eq << sets.el.imply.et.split.interval.apply(Eq[0])

    Eq <<= algebra.cond.imply.infer.apply(Eq[-2], cond=t > x), algebra.cond.imply.infer.apply(Eq[-1], cond=t <= x)

    Eq <<= algebra.infer.imply.infer.et.apply(Eq[-2]), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt.gt.imply.gt.transit), Eq[-1].this.rhs.apply(algebra.le.le.imply.le.transit)


if __name__ == '__main__':
    run()
# created on 2020-11-22
# updated on 2020-11-22
