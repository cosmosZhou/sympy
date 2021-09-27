from util import *


@apply(given=None)
def apply(given):
    A, B = given.of(Supset)
    return Equivalent(given, Subset(B, A), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << algebra.equivalent.given.et.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.supset.imply.subset.reverse)
    Eq << Eq[-1].this.rhs.apply(sets.supset.given.subset.reverse)


if __name__ == '__main__':
    run()
