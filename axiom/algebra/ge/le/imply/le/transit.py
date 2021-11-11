from util import *


@apply
def apply(b_greater_than_x, a_less_than_x):
    b, x = b_greater_than_x.of(GreaterEqual)
    a, _x = a_less_than_x.of(LessEqual)
    if x != _x:
        b, x, a, _x = _x, a, x, b
    assert x == _x
    return LessEqual(a, b)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(b >= x, a <= x)

    Eq << Eq[1].reversed

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-05-06
# updated on 2018-05-06
