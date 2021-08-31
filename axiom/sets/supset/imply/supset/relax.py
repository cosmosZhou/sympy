from util import *



@apply
def apply(given, S):
    lhs, rhs = given.of(Supset)
    return Supset(lhs | S, rhs)

@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    A, B, S = Symbol(etype=dtype.complex * n)

    Eq << apply(Supset(A, B), S)

    Eq << Eq[0].reversed

    Eq << sets.subset.imply.subset.relax.apply(Eq[-1], S)

    Eq << Eq[-1].reversed

if __name__ == '__main__':
    run()

