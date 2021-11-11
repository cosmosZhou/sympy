from util import *


@apply
def apply(is_nonnegative, le):
    x = is_nonnegative.of(Expr >= 0)
    _x, y = le.of(LessEqual)
    assert x == _x

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, x <= y)

    Eq << Eq[-1] - x ** 2

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.min)

    Eq << algebra.ge_zero.le.imply.le.square.apply(Eq[0], Eq[1])

    Eq << algebra.le.imply.ge_zero.apply(Eq[-1])

    Eq << algebra.ge.imply.eq.min.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-20
# updated on 2019-06-20
