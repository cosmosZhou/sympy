from util import *


@apply
def apply(self):
    interval, (k, n, _0) = self.of(Cup)
    assert _0 == 0
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert not interval.left_open and interval.right_open
    assert n <= 0

    return Equal(self, Interval(n, 0, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:-n:0](Interval(k, k + 1, right_open=True)))

    Eq << Eq[-1].this.lhs.apply(sets.cup.limits.subs.negate, k, -1 - k)

    Eq << Eq[-1].this.lhs.apply(sets.cup.to.interval.induct.negative.right_open)


if __name__ == '__main__':
    run()
# created on 2021-02-19
