from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, _x = le.of(LessEqual)
    assert x == _x

    return Equal(Max(y ** 2, x ** 2), y ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[-1] - y ** 2

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.max)

    Eq << algebra.le_zero.le.imply.ge.square.apply(Eq[0], Eq[1])

    Eq << algebra.ge.imply.le_zero.apply(Eq[-1])

    Eq << algebra.le.imply.eq.max.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-09-04
