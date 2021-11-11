from util import *


@apply
def apply(is_nonnegative, less_than):
    if not less_than.is_Less:
        less_than, is_nonnegative = given

    x = is_nonnegative.of(Expr >= 0)
    _x, M = less_than.of(Less)
    assert x == _x

    return Equal(Floor(x), 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << algebra.imply.le.floor.apply(x)

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[1])

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << algebra.imply.gt.floor.apply(x)

    Eq << algebra.gt.ge.imply.gt.transit.apply(Eq[-1], Eq[0] - 1)

    Eq << algebra.gt.imply.ge.strengthen.apply(Eq[-1])
    Eq <<= Eq[-4] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-21
# updated on 2018-10-21
