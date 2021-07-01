from util import *



@apply
def apply(*given):
    a_less_than_x, b_greater_than_x = given
    a, x = a_less_than_x.of(LessEqual)
    b, _x = b_greater_than_x.of(Greater)
    if b == a:
        a, x, b, _x = _x, a, x, b
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a = Symbol.a(real=True)
    x = Symbol.x(real=True)
    b = Symbol.b(real=True)

    Eq << apply(a <= x, b > x)

    Eq << Eq[1].reversed

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
