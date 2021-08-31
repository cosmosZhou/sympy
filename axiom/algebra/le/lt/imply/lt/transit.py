from util import *


@apply
def apply(le, lt):
    a, x = le.of(LessEqual)
    _x, b = lt.of(Less)
    if x != _x:
        a, x, _x, b = _x, b, a, x
        assert x == _x
    return Less(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True, given=True)
    Eq << apply(x <= a, b < x)

    Eq << ~Eq[-1]

    Eq << algebra.le.ge.imply.ge.transit.apply(Eq[0], Eq[-1])

    Eq <<= Eq[1] & Eq[-1]


if __name__ == '__main__':
    run()
