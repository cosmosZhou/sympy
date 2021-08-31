from util import *



@apply
def apply(a_less_than_x, b_greater_than_x):
    a, x = a_less_than_x.of(LessEqual)
    b, _x = b_greater_than_x.of(GreaterEqual)
    if x != _x:
        a, x, b, _x = _x, a, x, b
    assert x == _x
    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(real=True)

#     Eq << apply(a <= x, b >= x)
    Eq << apply(x <= a, x >= b)

    Eq << Eq[1].reversed

    Eq << algebra.le.le.imply.le.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
