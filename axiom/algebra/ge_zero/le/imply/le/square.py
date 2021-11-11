from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    _x, M = le.of(LessEqual)
    assert x == _x

    return LessEqual(x * x, M * M)


@prove
def prove(Eq):
    from axiom import algebra

    x, M = Symbol(real=True)
    Eq << apply(x >= 0, x <= M)

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[0], Eq[1])

    Eq << -Eq[-1]

    Eq << algebra.ge.le.imply.ge.transit.apply(Eq[0], Eq[-1])

    Eq << algebra.ge.le.imply.le_zero.apply(Eq[-1], Eq[1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] - Eq[-1].lhs.args[0]


if __name__ == '__main__':
    run()
# created on 2019-06-17
# updated on 2019-06-17
