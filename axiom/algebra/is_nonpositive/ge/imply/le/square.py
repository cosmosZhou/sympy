from util import *


@apply
def apply(is_nonpositive, greater_than):
    x = is_nonpositive.of(Expr <= 0)
    _x, m = greater_than.of(GreaterEqual)
    assert x == _x

    return LessEqual(x * x, m * m)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    m = Symbol.m(real=True)

    Eq << apply(x <= 0, x >= m)

    Eq << algebra.le.ge.imply.le.transit.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.le.ge.imply.le.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.ge.le.imply.is_nonpositive.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[0]


if __name__ == '__main__':
    run()
