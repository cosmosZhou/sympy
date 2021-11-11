from util import *
from axiom.sets.eq.imply.eq.swap import swap


@apply
def apply(imply, i=None, j=None):
    x, y = imply.of(Equal)
    assert len(x.shape) == 1

    assert x.dtype.is_set
    if i is None:
        i = Symbol.i(integer=True)

    if j is None:
        j = Symbol.j(integer=True)

    return Equal(swap[i, j](x), swap[i, j](y))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(positive=True, integer=True)

    x, y = Symbol(shape=(n,), etype=dtype.integer)

    Eq << apply(Equal(x, y))

    (i,), (j,) = Eq[1].lhs.limits
    Eq << sets.eq.imply.eq.swap.apply(Eq[1], i, j)

    Eq << sets.imply.eq.swap.apply(x, i, j)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << sets.imply.eq.swap.apply(y, i, j)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2021-03-30
# updated on 2021-03-30
