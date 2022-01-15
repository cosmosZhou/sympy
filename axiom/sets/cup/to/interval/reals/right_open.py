from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(-oo, oo, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, right_open=True)))

    Eq << Eq[0].this.lhs.apply(sets.cup.to.union.split, cond=k >= 0)

    Eq << Eq[-1].this.find(~Cup | Cup).apply(sets.cup.limits.subs.negate, k, -k - 1)

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.to.interval.infinity.right_open)

    Eq << Eq[-1].this.find(Cup).apply(sets.cup.to.interval.negative_infinity.right_open)


if __name__ == '__main__':
    run()
# created on 2021-02-18
