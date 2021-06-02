
from util import *

# given : A & B = A | B => A = B


@apply
def apply(given):
    assert given.is_Equal
    assert given.lhs.is_Intersection and given.rhs.is_Union or given.lhs.is_Union and given.rhs.is_Intersection
    A, B = given.lhs.args
    _A, _B = given.rhs.args
    assert A == _A and B == _B
    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equal(A & B, A | B))

    Eq << Subset(A, A | B, plausible=True).subs(Eq[0].reversed)
    Eq << Subset(A & B, B, plausible=True)

    Eq.subset = sets.subset.subset.imply.subset.transit.apply(Eq[-2], Eq[-1])

    Eq << Subset(B, A | B, plausible=True).subs(Eq[0].reversed)
    Eq << Subset(A & B, A, plausible=True)

    Eq <<= sets.subset.subset.imply.subset.transit.apply(Eq[-2], Eq[-1])

    Eq <<= Eq[-1] & Eq.subset

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

