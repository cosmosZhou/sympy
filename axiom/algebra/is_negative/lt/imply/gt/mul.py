from util import *


@apply
def apply(is_positive_x, strict_less_than):
    x = is_positive_x.of(Expr < 0)
    lhs, rhs = strict_less_than.of(Less)
    return Greater(lhs * x, rhs * x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a < b)

    Eq << Eq[1] - b

    Eq << algebra.is_negative.is_negative.imply.is_positive.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
