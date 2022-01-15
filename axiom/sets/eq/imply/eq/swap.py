from util import *
from axiom.sets.imply.eq.swap import swap


@apply
def apply(given, i=None, j=None):
    x, y = given.of(Equal)
    assert len(x.shape) == 1

    assert x.dtype.is_set
    if i is None:
        i = Symbol.i(integer=True)

    if j is None:
        j = Symbol.j(integer=True)

    return Equal(swap[i, j](x), swap[i, j](y))


@prove
def prove(Eq):
    n = Symbol(positive=True, integer=True)

    x, y = Symbol(shape=(n,), etype=dtype.integer)

    Eq << apply(Equal(x, y))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2021-03-29
