
from util import *
import axiom


@apply
def apply(*given):
    a_less_than_x, x_less_than_b = given
    a, x = a_less_than_x.of(LessEqual)
    _x, b = x_less_than_b.of(Less)
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, x < b)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
