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
    x = Symbol(real=True)
    a = Symbol(real=True, nonnegative=True)

    Eq << apply(x >= 0, x <= a)

    Eq << Eq[1].reversed - x

    Eq << algebra.ge_zero.ge_zero.imply.ge_zero.apply(Eq[-1], Eq[0])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2019-06-21
# updated on 2019-06-21
