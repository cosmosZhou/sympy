from util import *

import axiom


@apply
def apply(*given):
    a_less_than_x, b_greater_than_x = given
    a, x = a_less_than_x.of(LessEqual)
    b, _x = b_greater_than_x.of(GreaterEqual)
    if x != _x:
        x, a, _x, b = b, _x, a, x
    assert x == _x
    return LessEqual(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, b >= x)

    Eq << Eq[1].reversed

    Eq << algebra.le.le.imply.le.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()