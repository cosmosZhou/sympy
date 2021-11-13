from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    y, _x = lt.of(Less)
    assert x == _x
    return Greater(y ** 2, x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, y = Symbol(real=True)
    Eq << apply(x <= 0, y < x)

    Eq << Eq[1] + x

    Eq << Eq[0] * 2

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.imply.lt_zero.apply(Eq[1])

    Eq << algebra.lt_zero.lt_zero.imply.gt_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.apply(algebra.gt.transposition, lhs=0)


if __name__ == '__main__':
    run()
# created on 2019-12-09
# updated on 2019-12-09