from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(-1, 1, left_open=True, right_open=True)
    return sqrt(1 - x ** 2) > 0


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(-1, 1, left_open=True, right_open=True)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq <<= Eq[-2] + 1, Eq[-1] - 1

    Eq << -Eq[-2]

    Eq << algebra.lt_zero.lt_zero.imply.gt_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-11-26
