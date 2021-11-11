from util import *


@apply
def apply(is_negative, strict_less_than):
    x = is_negative.of(Expr < 0)
    assert x.is_finite
    lhs, rhs = strict_less_than.of(Less)
    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a < b)

    Eq << algebra.lt_zero.imply.lt_zero.div.apply(Eq[0])

    Eq << algebra.lt_zero.lt.imply.gt.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-07-15
# updated on 2019-07-15
