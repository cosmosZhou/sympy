from util import *


@apply
def apply(x_less_than_y, x_less_than_b):
    x, y = x_less_than_y.of(Less)
    _x, b = x_less_than_b.of(Less)
    assert x == _x
    return Less(x, Min(y, b))


@prove
def prove(Eq):
    from axiom import algebra
    x, y, b = Symbol(real=True, given=True)


    Eq << apply(x < y, x < b)

    Eq << Eq[-1].this.rhs.apply(algebra.min.to.piece)

    Eq << algebra.cond.given.ou.apply(Eq[-1])

    Eq << ~Eq[-1]

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[0], Eq[-1], invert=True, reverse=True)

    Eq << algebra.cond.cond.imply.cond.subs.apply(Eq[1], Eq[-1], invert=True, reverse=True)


if __name__ == '__main__':
    run()

from . import both
