from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    _x, y = lt.of(Less)
    assert x == _x

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, x < y)

    Eq << algebra.lt.imply.le.relax.apply(Eq[1])

    Eq << algebra.ge_zero.le.imply.eq.min.apply(Eq[0], Eq[-1])












if __name__ == '__main__':
    run()
# created on 2019-07-02
# updated on 2019-07-02
