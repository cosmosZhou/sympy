from util import *


@apply
def apply(is_negative_y, is_positive_x):
    x = is_positive_x.of(Expr > 0)
    y = is_negative_y.of(Expr < 0)
    return Less(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(y < 0, x > 0)

    Eq << -Eq[0]

    Eq << algebra.gt_zero.gt_zero.imply.gt_zero.apply(Eq[-1], Eq[1])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-12-14
