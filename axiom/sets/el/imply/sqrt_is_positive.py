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

    Eq << sets.el.imply.et.split.interval.apply(Eq[0])

    Eq <<= Eq[-2] + 1, Eq[-1] - 1

    Eq << -Eq[-2]

    Eq << algebra.is_negative.is_negative.imply.is_positive.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.is_positive.imply.sqrt_is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()