from util import *



@apply
def apply(a_less_than_x, b_greater_than_x):
    a, x = a_less_than_x.of(Less)
    b, _x = b_greater_than_x.of(GreaterEqual)
    if x != _x:
        b, _x, a, x = x, a, _x, b
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

    Eq << apply(a < x, b >= x)

    Eq << Eq[1].reversed

    Eq << algebra.lt.le.imply.lt.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-18
# updated on 2018-10-18
