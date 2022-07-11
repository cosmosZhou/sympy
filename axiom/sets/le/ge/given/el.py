from util import *


@apply
def apply(le, ge):
    a, x = le.of(LessEqual)
    b, _x = ge.of(GreaterEqual)

    if x != _x:
        a, x, _x, b = _x, b, a, x

    assert x == _x

    return Element(x, Interval(a, b, left_open=False, right_open=False))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True)
    Eq << apply(a <= x, b >= x)

    Eq << sets.el_interval.imply.et.apply(Eq[-1])

    Eq << Eq[-1].reversed

    Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()
# created on 2021-05-16
