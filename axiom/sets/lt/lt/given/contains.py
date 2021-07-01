from util import *


@apply
def apply(lt0, lt1):
    x, a = lt0.of(Less)
    b, _x = lt1.of(Less)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    else:
        ...

    assert x == _x

    return Contains(x, Interval(b, a, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    x = Symbol.x(real=True)
    Eq << apply(a < x, x < b)

    Eq << sets.contains.imply.et.split.interval.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()