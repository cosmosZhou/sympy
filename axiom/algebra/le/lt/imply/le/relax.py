from util import *


@apply
def apply(le, lt):
    a, x = le.of(LessEqual)
    _x, b = lt.of(Less)
    if x != _x:
        a, x, _x, b = _x, b, a, x
        assert x == _x

    return LessEqual(a, b)


@prove
def prove(Eq):
    from axiom import algebra

    a, x, b = Symbol(real=True, given=True)
    Eq << apply(a <= x, x < b)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[0], Eq[1])

    Eq << algebra.lt.imply.le.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-11-24
# updated on 2019-11-24
