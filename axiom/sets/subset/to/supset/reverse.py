from util import *


@apply(given=None)
def apply(given):
    A, B = given.of(Subset)
    return Equivalent(given, Supset(B, A), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])
    Eq << Eq[-2].this.lhs.apply(sets.subset.imply.supset.reverse)
    Eq << Eq[-1].this.rhs.apply(sets.subset.given.supset.reverse)


if __name__ == '__main__':
    run()