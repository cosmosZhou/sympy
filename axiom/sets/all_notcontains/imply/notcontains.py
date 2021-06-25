from util import *


@apply
def apply(given):
    (e, S), *limits = given.of(All[NotContains])

    return NotContains(e, Cup(S, *limits))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(All[k:n](NotContains(x, A[k])))

    Eq << sets.imply.suffice.notcontains.induct.apply(Eq[0].function, n)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

