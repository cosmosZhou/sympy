from util import *


@apply
def apply(x_less_than_y, x_greater_than_y_minus):
    x, y = x_less_than_y.of(Less)
    _x, _y = x_greater_than_y_minus.of(Greater)
    assert x == _x
    assert y + _y == 0
    return Less(abs(x), abs(y))


@prove
def prove(Eq):
    from axiom import algebra
    y, x = Symbol(real=True)

    Eq << apply(x < y, x > -y)

    Eq << algebra.lt.gt.imply.gt.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + y

    Eq << Eq[-1] / 2

    Eq << algebra.is_positive.imply.eq.abs.apply(Eq[-1])

    Eq << algebra.lt.gt.imply.lt.abs.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + Eq[-2].reversed

    Eq << Eq[-1].this.apply(algebra.lt.simplify.common_terms)

if __name__ == '__main__':
    run()
