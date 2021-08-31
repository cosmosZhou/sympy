from util import *


@apply
def apply(is_nonnegative, gt):
    x = is_nonnegative.of(Expr >= 0)
    y, _x = gt.of(Greater)
    assert _x == x
    return Greater(sqrt(y), sqrt(x))


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[1], Eq[0])

    Eq << algebra.is_positive.imply.sqrt_is_positive.apply(Eq[-1])

    Eq << algebra.is_nonnegative.imply.sqrt_is_nonnegative.apply(Eq[0])

    Eq.is_positive = algebra.gt.ge.imply.gt.add.apply(Eq[-2], Eq[-1])

    Eq << algebra.gt.imply.is_positive.apply(Eq[1])

    Eq << algebra.is_positive.gt.imply.gt.div.apply(Eq.is_positive, Eq[-1])

    Eq << ((sqrt(x) + sqrt(y))(-sqrt(x) + sqrt(y))).this.apply(algebra.mul.to.add, deep=True)

    Eq << algebra.is_positive.eq.imply.eq.div.apply(Eq.is_positive, Eq[-1])
    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << algebra.gt.given.is_positive.apply(Eq[2])


if __name__ == '__main__':
    run()