from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(-1, 1)
    return sqrt(1 - x ** 2) >= 0


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(-1, 1)))

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq <<= Eq[-2] + 1, Eq[-1] - 1

    Eq << -Eq[-2]

    Eq << algebra.le_zero.le_zero.imply.ge_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.ge_zero.imply.sqrt_ge_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-14
