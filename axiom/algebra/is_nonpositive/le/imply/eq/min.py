from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, _x = le.of(LessEqual)
    assert x == _x

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[-1] - x ** 2

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.min)

    Eq << algebra.is_nonpositive.le.imply.le.square.apply(Eq[0], Eq[1])

    Eq << algebra.le.imply.is_nonnegative.apply(Eq[-1])

    Eq << algebra.ge.imply.eq.min.apply(Eq[-1])


if __name__ == '__main__':
    run()