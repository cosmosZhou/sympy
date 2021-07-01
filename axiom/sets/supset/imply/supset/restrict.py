from util import *




@apply
def apply(given, S):
    lhs, rhs = given.of(Supset)
    return Supset(lhs, rhs & S)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    B = Symbol.B(etype=dtype.complex * n)
    S = Symbol.S(etype=dtype.complex * n)

    Eq << apply(Supset(A, B), S)

    Eq << Eq[0].reversed

    Eq << sets.subset.imply.subset.restrict.apply(Eq[-1], S)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

