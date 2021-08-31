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
    from axiom import sets, calculus

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, right_open=True)))

    n = Symbol(integer=True, positive=True)
    Eq << sets.cup.to.interval.induct.negative.right_open.apply(Cup[k:n](Interval(-k - 1, -k, right_open=True)))

    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.rhs.apply(calculus.limit.to.interval)

    Eq << Eq[-1].this.lhs.apply(calculus.limit.to.cup)


if __name__ == '__main__':
    run()
