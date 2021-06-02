from util import *
import axiom



@apply
def apply(*given):
    x_less_than_y, neg_x_less_than_y = given
    x, y = x_less_than_y.of(Less)
    _x, _y = neg_x_less_than_y.of(Less)
    assert x == -_x
    assert y == _y
    return Less(abs(x), y)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)

    Eq << apply(x < y, -x < y)

    Eq << Eq[0] - y

    Eq << Eq[1] - y

    Eq << algebra.is_negative.is_negative.imply.is_positive.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expand() + x * x

    Eq << Eq[-1].reversed

    Eq.lt = algebra.lt.imply.lt.sqrt.apply(Eq[-1])

    Eq << algebra.lt.gt.imply.gt.transit.apply(Eq[0], -Eq[1])

    Eq << (Eq[-1] + y) / 2

    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[-1])

    Eq << Eq.lt.subs(Eq[-1])


if __name__ == '__main__':
    run()

del add
from . import add
from . import sub
del mul
from . import mul
