from util import *


@apply
def apply(x_less_than_y, x_greater_than_y_minus):
    x, a = x_less_than_y.of(Less)
    _x, b = x_greater_than_y_minus.of(Greater)
    assert x == _x
    return Less(abs(x), Max(abs(a), abs(b)))


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True, given=True)

    Eq << apply(x < a, x > b)

    Eq << algebra.lt_abs.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-2], - ~Eq[-1]

    Eq <<= algebra.ge.imply.ge.relax.apply(Eq[-2], abs(a)), -algebra.ge.imply.ge.relax.apply(Eq[-1], abs(b))

    Eq <<= algebra.lt.ge.imply.gt.transit.apply(Eq[0], Eq[-2]), -algebra.gt.le.imply.lt.transit.apply(Eq[1], Eq[-1])

    Eq <<= algebra.imply.le.abs.apply(a), algebra.imply.le.abs.apply(b, negate=True)

    Eq <<= Eq[-2] & Eq[-4], Eq[-1] & Eq[-3]


if __name__ == '__main__':
    run()
