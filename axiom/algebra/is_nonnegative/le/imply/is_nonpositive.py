from util import *


@apply
def apply(is_nonnegative, less_than):
    x = is_nonnegative.of(Expr >= 0)
    _x, a = less_than.of(LessEqual)
    assert x == _x
    return LessEqual(x * (x - a), 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, nonnegative=True)

    Eq << apply(x >= 0, x <= a)

    Eq << Eq[1].reversed - x

    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.apply(Eq[-1], Eq[0])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()
