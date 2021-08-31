from util import *


@apply
def apply(is_nonpositive, lt):
    x = is_nonpositive.of(Expr <= 0)
    M, _x = lt.of(Less)
    assert x == _x

    return Less(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x <= 0, M < x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.le.gt.imply.gt.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.lt.gt.imply.is_negative.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[0]


if __name__ == '__main__':
    run()