from util import *


@apply
def apply(ge):
    x, a = ge.of(Greater)
    assert a > 0

    return Less(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x > a)

    Eq << algebra.gt.imply.gt_zero.transit.apply(Eq[0])

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq << algebra.gt_zero.gt.imply.gt.mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * a


if __name__ == '__main__':
    run()
# created on 2019-07-28
# updated on 2019-07-28
