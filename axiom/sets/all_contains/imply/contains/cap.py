from util import *


@apply
def apply(given):
    (x, A), *limits = given.of(ForAll[Contains])
    return Contains(x, Cap(A, *limits))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(positive=True, integer=True, given=False)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(ForAll[k:n](Contains(x, A[k])))

    Eq << sets.imply.suffice.contains.induct.apply(Contains(x, A[k]), n)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

