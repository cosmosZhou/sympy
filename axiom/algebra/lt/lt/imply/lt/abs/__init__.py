from util import *


@apply
def apply(x_less_than_y, neg_x_less_than_y):
    x, y = x_less_than_y.of(Less)
    _x, _y = neg_x_less_than_y.of(Less)
    assert x == -_x
    assert y == _y
    return Less(abs(x), y)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True)

    Eq << apply(x < y, -x < y)

    Eq << Eq[0] - y

    Eq << Eq[1] - y

    Eq << algebra.lt_zero.lt_zero.imply.gt_zero.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expand() + x * x

    Eq << Eq[-1].reversed

    Eq.lt = algebra.lt.imply.lt.sqrt.apply(Eq[-1])

    Eq << algebra.lt.gt.imply.gt.transit.apply(Eq[0], -Eq[1])

    Eq << (Eq[-1] + y) / 2

    Eq << algebra.gt_zero.imply.eq.abs.apply(Eq[-1])

    Eq << Eq.lt.subs(Eq[-1])


if __name__ == '__main__':
    run()

from . import add
from . import sub
from . import mul
# created on 2019-12-30
