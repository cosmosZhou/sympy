from util import *


@apply
def apply(ge, lt):
    b, x = ge.of(GreaterEqual)
    a, _x = lt.of(Less)
    if x != _x:
        x, b, _x, a = a, _x, b, x
    assert x == _x

    return GreaterEqual(b, a)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True)
    Eq << apply(b >= x, a < x)

    Eq << algebra.ge.lt.imply.gt.transit.apply(Eq[0], Eq[1])
    Eq << algebra.gt.imply.ge.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-09-03
