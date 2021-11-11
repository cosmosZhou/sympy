from util import *


@apply
def apply(x_less_than_y, x_greater_than_y_minus):
    x, y = x_less_than_y.of(LessEqual)
    _x, _y = x_greater_than_y_minus.of(GreaterEqual)
    assert _x == x
    assert y + _y == 0
    return LessEqual(abs(x), y)


@prove
def prove(Eq):
    from axiom import algebra

    y, x = Symbol(real=True)
    Eq << apply(x <= y, x >= -y)

    Eq << Eq[-1].this.lhs.apply(algebra.abs.to.piece)

    Eq << Eq[-1].apply(algebra.cond.given.ou)

    Eq << algebra.cond.given.et.restrict.apply(Eq[-1], cond=Eq[0])

    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1])



    Eq << -Eq[1]

    Eq << algebra.cond.given.et.restrict.apply(Eq[-2], cond=Eq[-1])

    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1])


if __name__ == '__main__':
    run()
from . import both
# created on 2018-06-27
# updated on 2018-06-27
