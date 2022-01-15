from util import *


@apply
def apply(self):
    interval, (k, a, b) = self.of(Cup)
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from axiom import algebra, sets

    k, a, b = Symbol(integer=True)
    Eq << apply(Cup[k:a:b](Interval(k, k + 1, left_open=True)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=a < b)

    Eq << Eq[-2].this.lhs.apply(sets.lt.imply.eq.cup.to.interval.left_open, k)

    Eq << (a >= b).this.apply(sets.ge.imply.interval_is_empty, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.given.et.subs)

    Eq << algebra.infer.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.piece)

    Eq << (a >= b).this.apply(sets.ge.imply.range_is_empty)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.given.et.subs)


if __name__ == '__main__':
    run()
from . import negative
# created on 2018-10-20
