from util import *


@apply
def apply(is_positive_x, lt):
    x = is_positive_x.of(Expr > 0)
    assert x.is_finite
    lhs, rhs = lt.of(Less)
    return Less(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a < b)

    Eq << algebra.gt_zero.imply.gt_zero.div.apply(Eq[0])

    Eq << algebra.gt_zero.lt.imply.lt.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-06-27
# updated on 2019-06-27
