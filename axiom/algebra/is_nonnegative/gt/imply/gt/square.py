from util import *


@apply
def apply(is_nonnegative, strict_greater_than):
    x = is_nonnegative.of(Expr >= 0)
    y, _x = strict_greater_than.of(Greater)
    assert x == _x
    return Greater(y ** 2, x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, y = Symbol(real=True)
    Eq << apply(x >= 0, y > x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-1], Eq[-2])

    Eq << algebra.gt.imply.is_positive.apply(Eq[1])

    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.apply(algebra.gt.transposition, lhs=0)


if __name__ == '__main__':
    run()