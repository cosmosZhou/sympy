from util import *


import axiom


@apply
def apply(given):
    assert given.is_Subset
    B, A = given.args
    e = B.of(FiniteSet)

    return Contains(e, A)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    e = Symbol.e(complex=True, shape=(n,))
    B = {e}

    Eq << apply(Subset(B, A))

    Eq << sets.subset.imply.all_contains.apply(Eq[0])


if __name__ == '__main__':
    run()

