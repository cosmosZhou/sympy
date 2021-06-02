from util import *
import axiom



@apply
def apply(*given):
    x1_less_than_y, y_less_than_x = given
    x1, y = x1_less_than_y.of(Less)
    _y, x = y_less_than_x.of(LessEqual)
    assert y == _y
    assert x1 + 1 == x
    assert y.is_integer

    return Equal(y, floor(x))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(integer=True)

    Eq << apply(x - 1 < y, y <= x)

    Eq << Eq[0] - y + 1

    Eq << (Eq[1] - y).reversed

    Eq << algebra.is_nonnegative.lt.imply.eq.frac.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.rhs.apply(algebra.frac.to.add)


if __name__ == '__main__':
    run()
