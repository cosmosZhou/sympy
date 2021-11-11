from util import *


@apply
def apply(self):
    interval, (k, _0, n) = self.of(Cup)
    assert _0 == 0
    _k, k1 = interval.of(Interval)
    assert k == _k and k1 == k + 1
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(0, n, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:n](Interval(k, k + 1, right_open=True)))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cup.to.union.split, cond={n})

    Eq << sets.eq.imply.eq.union.apply(Eq[0], Interval(n, n + 1, right_open=True))

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.eq.induct.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2021-02-12
# updated on 2021-02-12
