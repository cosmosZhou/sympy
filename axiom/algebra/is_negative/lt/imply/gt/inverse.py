from util import *


@apply
def apply(is_positive, ge):
    a = is_positive.of(Expr < 0)
    x, a = ge.of(Less)

    return Greater(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(a < 0, x < a)

    Eq << ~Eq[-1]

    Eq << algebra.is_negative.imply.is_nonzero.apply(Eq[0])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq.x_is_negative = algebra.lt.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.is_negative.imply.is_nonzero.apply(Eq.x_is_negative)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq << algebra.is_negative.is_negative.imply.is_positive.apply(Eq[0], Eq.x_is_negative)

    Eq << ~algebra.is_positive.le.imply.le.mul.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()