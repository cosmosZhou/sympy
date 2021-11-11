from util import *


@apply
def apply(is_negative, strict_greater_than):
    x = is_negative.of(Expr < 0)
    assert x.is_finite
    lhs, rhs = strict_greater_than.of(Greater)
    return Less(lhs * x, rhs * x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a > b)

    Eq << Eq[1] - b

    Eq << algebra.lt_zero.gt_zero.imply.lt_zero.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
# created on 2019-12-15
# updated on 2019-12-15
