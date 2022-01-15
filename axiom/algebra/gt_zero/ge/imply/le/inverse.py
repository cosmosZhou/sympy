from util import *


@apply
def apply(is_positive, ge):
    a = is_positive.of(Expr > 0)
    x, a = ge.of(GreaterEqual)

    return LessEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(a > 0, x >= a)

    Eq << ~Eq[-1]

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq.x_is_positive = algebra.gt.ge.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq.x_is_positive)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[0], Eq.x_is_positive)

    Eq << ~algebra.gt_zero.gt.imply.gt.mul.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()
# created on 2019-08-09
