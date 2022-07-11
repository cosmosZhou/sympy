from util import *


@apply
def apply(lt, gt):
    a, x = lt.of(Less)
    b, _x = gt.of(Greater)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    else:
        ...

    assert x == _x

    return Element(x, Interval(a, b, left_open=True, right_open=True))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(real=True)
    Eq << apply(a < x, b > x)

    Eq << sets.el_interval.imply.et.apply(Eq[-1])

    Eq << Eq[-1].reversed

    Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()
# created on 2021-05-28
