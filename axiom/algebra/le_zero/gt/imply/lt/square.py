from util import *


@apply
def apply(is_nonpositive, greater_than):
    x = is_nonpositive.of(Expr <= 0)
    _x, m = greater_than.of(Greater)
    assert x == _x

    return Less(x * x, m * m)


@prove
def prove(Eq):
    from axiom import algebra

    x, m = Symbol(real=True)
    Eq << apply(x <= 0, x > m)

    Eq << algebra.le.gt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.le.gt.imply.lt.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.lt.gt.imply.lt_zero.apply(Eq[-1], Eq[1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[0]


if __name__ == '__main__':
    run()
# created on 2019-08-30
# updated on 2019-08-30
