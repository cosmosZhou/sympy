from util import *


@apply
def apply(ge):
    x, a = ge.of(Less)
    assert x > 0

    return Greater(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True, positive=True)
    a = Symbol(real=True)
    Eq << apply(x < a)

    Eq << algebra.lt.imply.gt_zero.transit.apply(Eq[0])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq << algebra.gt_zero.lt.imply.lt.mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * x

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-12-29
# updated on 2019-12-29
