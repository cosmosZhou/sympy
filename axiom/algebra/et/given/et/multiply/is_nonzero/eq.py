from util import *

import axiom


@apply
def apply(given):
    is_nonzero, eq = given.of(And)
    if not eq.is_Equal:
        is_nonzero, eq = eq, is_nonzero
    x = is_nonzero.of(Unequal[0])
    a, b = eq.of(Equal)
    return is_nonzero & Equal((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    z = Symbol.z(integer=True)

    Eq << apply(Equal(1 / x + y, z) & Unequal(x, 0))

    Eq << Eq[-1].apply(algebra.is_nonzero.eq.imply.eq.divide)

    Eq << algebra.et.imply.cond.apply(Eq[1], index=0)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

