from util import *


@apply
def apply(b_greater_than_x, a_less_than_x):
    b, x = b_greater_than_x.of(Greater)
    a, _x = a_less_than_x.of(LessEqual)
    if x != _x:
        x, b, _x, a = a, _x, b, x
    assert x == _x

    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(b > x, a <= x)

    Eq << Eq[1].reversed

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-07-30
# updated on 2019-07-30
