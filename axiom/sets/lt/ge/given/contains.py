from util import *


@apply
def apply(lt, ge):
    a, x = lt.of(Less)
    b, _x = ge.of(GreaterEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        left_open = True
        right_open = False
    else:
        left_open = True
        right_open = False

    assert x == _x

    return Contains(x, Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    Eq << apply(a < x, b >= x)

    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])

    Eq << Eq[-1].reversed

    Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()