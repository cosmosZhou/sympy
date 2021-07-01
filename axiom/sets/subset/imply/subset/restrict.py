from util import *



@apply
def apply(given, S):
    lhs, rhs = given.of(Subset)
    return Subset(lhs & S, rhs)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)

    Eq << apply(Subset(A, B), S)

    Eq << Subset(A & S, A, plausible=True)

    Eq << sets.subset.subset.imply.subset.transit.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

