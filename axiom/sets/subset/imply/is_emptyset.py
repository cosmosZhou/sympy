from util import *


@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equal(A // B, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Subset(A, B))

    Eq << ~Eq[-1]

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.function.apply(sets.contains.imply.et.split.complement, simplify=None)

    Eq << sets.any_et.imply.any.single_variable.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << sets.any.imply.any.limits.swap.apply(Eq[-1])

    Eq << Eq[-1].this.function.apply(sets.contains.subset.imply.contains, Eq[0])

    Eq << algebra.any.imply.any_et.single_variable.apply(Eq[-1])


if __name__ == '__main__':
    run()
