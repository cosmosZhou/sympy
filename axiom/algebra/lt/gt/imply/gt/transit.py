from util import *


@apply
def apply(lt, gt):
    a, x = lt.of(Less)
    b, _x = gt.of(Greater)
    if x != _x:
        b, _x, a, x = x, a, _x, b
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a < x, b > x)

    Eq << Eq[1].reversed

    Eq << algebra.lt.lt.imply.lt.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
