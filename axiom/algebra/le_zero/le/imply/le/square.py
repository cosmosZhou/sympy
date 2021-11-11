from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    M, _x = le.of(LessEqual)
    assert x == _x

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x <= 0, M <= x)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.le.ge.imply.ge.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.le.ge.imply.le_zero.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[0]


if __name__ == '__main__':
    run()
# created on 2019-12-07
# updated on 2019-12-07
