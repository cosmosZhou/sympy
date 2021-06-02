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
    from axiom import sets, calculus

    k = Symbol.k(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, left_open=True)))

    n = Symbol.n(integer=True, positive=True)
    Eq << sets.cup.to.interval.induct.left_open.apply(Cup[k:n](Interval(k, k + 1, left_open=True)))

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.apply(calculus.limit.to.interval)

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.cup)


if __name__ == '__main__':
    run()