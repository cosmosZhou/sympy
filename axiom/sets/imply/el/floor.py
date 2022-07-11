from util import *


@apply
def apply(n, d):
    assert d > 0
    return Element(n - d * Floor(n / d), Interval(0, d, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(real=True)
    d = Symbol(real=True, positive=True)
    Eq << apply(n, d)

    Eq << sets.el_interval.given.et.apply(Eq[0])

    Eq << algebra.imply.le.floor.apply(Eq[0].find(Floor).arg)

    Eq << algebra.le.imply.le.mul.apply(Eq[-1], d)

    Eq << -Eq[-1] + n

    Eq << algebra.imply.lt.floor.apply(Eq[0].find(Floor).arg) - 1

    Eq << Eq[-1] * d

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    Eq << -Eq[-1] + n

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-06-18
