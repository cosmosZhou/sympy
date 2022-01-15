from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    _x, M = lt.of(Less)
    assert x == _x

    return Equal(x, frac(x))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << Eq[-1].this.rhs.apply(algebra.frac.to.add).reversed

    Eq << algebra.ge_zero.lt.imply.floor_is_zero.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-03-07
