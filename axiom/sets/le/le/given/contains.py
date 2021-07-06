from util import *


@apply
def apply(le0, le1):
    x, a = le0.of(LessEqual)
    b, _x = le1.of(LessEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x

    assert x == _x

    return Contains(x, Interval(b, a, left_open=False, right_open=False))


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    Eq << apply(a <= x, x <= b)

    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()