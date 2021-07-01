from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Subset)
    return Subset(lhs & S, rhs & S)

@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)

    Eq << apply(Subset(A, B), S)

    Eq << sets.subset.imply.subset.restrict.apply(Eq[0], S)

    Eq << Subset(A & S, S, plausible=True)

    Eq <<= Eq[-1] & Eq[-2]

if __name__ == '__main__':
    run()


