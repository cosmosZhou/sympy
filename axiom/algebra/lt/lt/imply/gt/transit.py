from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(Less)
    _x, b = x_less_than_b.of(Less)
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a < x, x < b)

    Eq << algebra.lt.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2020-01-06
