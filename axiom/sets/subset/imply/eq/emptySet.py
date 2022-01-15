from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    assert B.is_EmptySet

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, A.emptySet))

    Eq << sets.subset.imply.eq.intersect.apply(Eq[0])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-09-14
