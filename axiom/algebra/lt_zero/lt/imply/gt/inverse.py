from util import *


@apply
def apply(is_positive, ge):
    a = is_positive.of(Expr < 0)
    x, a = ge.of(Less)

    return Greater(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(a < 0, x < a)

    Eq << ~Eq[-1]

    Eq << algebra.lt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq.x_is_negative = algebra.lt.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.lt_zero.imply.ne_zero.apply(Eq.x_is_negative)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq << algebra.lt_zero.lt_zero.imply.gt_zero.apply(Eq[0], Eq.x_is_negative)

    Eq << ~algebra.gt_zero.le.imply.le.mul.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()
# created on 2020-01-22
