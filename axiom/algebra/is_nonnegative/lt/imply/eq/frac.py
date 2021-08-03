from util import *


@apply
def apply(is_nonnegative, less_than):
    if not less_than.is_Less:
        less_than, is_nonnegative = given

    x = is_nonnegative.of(Expr >= 0)
    _x, M = less_than.of(Less)
    assert x == _x

    return Equal(x, frac(x))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << Eq[-1].this.rhs.apply(algebra.frac.to.add).reversed

    Eq << algebra.is_nonnegative.lt.imply.floor_is_zero.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
