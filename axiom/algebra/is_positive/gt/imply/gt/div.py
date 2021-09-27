from util import *


@apply
def apply(is_positive, gt):
    x = is_positive.of(Expr > 0)
    assert x.is_finite
    lhs, rhs = gt.of(Greater)
    return Greater(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a > b)

    Eq << algebra.is_positive.imply.is_positive.div.apply(Eq[0])

    Eq << algebra.is_positive.gt.imply.gt.mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
