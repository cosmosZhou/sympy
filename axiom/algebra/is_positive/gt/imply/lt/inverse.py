from util import *


@apply
def apply(is_positive, ge):
    a = is_positive.of(Expr > 0)
    if a is None:
        is_positive, ge = ge, is_positive
        a = is_positive.of(Expr > 0)
    x, a = ge.of(Greater)

    return Less(1 / x, 1 / a)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    Eq << apply(a > 0, x > a)

    Eq << ~Eq[-1]

    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq[0])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq.x_is_positive = algebra.gt.gt.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.is_positive.imply.is_nonzero.apply(Eq.x_is_positive)

    Eq << algebra.cond.ou.imply.cond.apply(Eq[-1], Eq[-2])

    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[0], Eq.x_is_positive)

    Eq << ~algebra.is_positive.ge.imply.ge.mul.apply(Eq[-1], Eq[-2]).reversed


if __name__ == '__main__':
    run()