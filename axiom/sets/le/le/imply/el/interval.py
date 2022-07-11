from util import *


@apply
def apply(le, _le):
    x, a = le.of(LessEqual)
    b, _x = _le.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x

    return Element(x, Interval(b, a))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True, given=True)
    #Eq << apply(x >= b, a >= x)
    Eq << apply(x <= b, a <= x)

    Eq << sets.el_interval.given.et.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-05-23
