from util import *

import axiom
from axiom.algebra.eq.eq.imply.eq.transit import transit


@apply
def apply(imply, swap=False, reverse=False):
    ab, bc = imply.of(And)
    if swap:
        ab, bc = bc, ab
    ac = transit(ab, bc, reverse=reverse)
    return ab, ac


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(integer=True, shape=(oo,))
    b = Symbol.b(integer=True, shape=(oo,))
    c = Symbol.c(integer=True, shape=(oo,))

    S = Symbol.S(etype=dtype.integer)

    Eq << apply(Equal(a[i], b[i]) & Equal(b[i], c[i]))

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[1], Eq[2])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

