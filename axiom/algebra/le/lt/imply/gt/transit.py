from util import *


@apply
def apply(le, lt):
    a, x = le.of(LessEqual)
    _x, b = lt.of(Less)
    if x != _x:
        a, x, _x, b = _x, a, b, x
    assert x == _x
    return Greater(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x <= a, b < x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
