from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(LessEqual)
    _x, b = x_less_than_b.of(LessEqual)
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a <= x, x <= b)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-11-19
# updated on 2019-11-19
