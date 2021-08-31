from util import *


@apply
def apply(self):
    interval, (k, _0, n) = self.of(Cup)
    assert _0 == 0
    _k1, _k = interval.of(Interval)
    assert _k == -k and _k1 == -k - 1
    assert interval.left_open and not interval.right_open
    assert n >= 0
    return Equal(self, Interval(-n, 0, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, nonnegative=True, given=False)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:n](Interval(-k - 1, -k, left_open=True)))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(sets.cup.to.union.split, cond={n})

    Eq << sets.eq.imply.eq.union.apply(Eq[0], Interval(-n - 1, -n, left_open=True))

    Eq << Suffice(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.suffice.imply.eq.induct.apply(Eq[-1], n=n, start=0)


if __name__ == '__main__':
    run()
