from util import *


@apply
def apply(a_less_than_b, x_less_than_y):
    a, b = a_less_than_b.of(Less)
    x, y = x_less_than_y.of(Less)

    assert a >= 0
    assert x >= 0
    return Less(a * x, b * y)


@prove
def prove(Eq):
    from axiom import algebra
    a, x = Symbol(real=True, nonnegative=True)
    b, y = Symbol(real=True)

    Eq << apply(a < b, x < y)

    Eq << Eq[2] - x * b

    Eq << Eq[-1].this.lhs.collect(x)

    Eq << Eq[-1].this.rhs.collect(b)

    Eq << Eq[0].reversed

    Eq << algebra.gt.imply.gt.relax.apply(Eq[-1], 0)

    Eq << Eq[1] - x

    Eq.is_positive = algebra.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[-2])

    Eq << Eq[0] - a

    Eq << -Eq[-1]

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq << algebra.is_negative.is_nonnegative.imply.is_nonpositive.apply(Eq[-2], Eq[-1])

    Eq << algebra.gt.le.imply.lt.transit.apply(Eq.is_positive, Eq[-1])



if __name__ == '__main__':
    run()
