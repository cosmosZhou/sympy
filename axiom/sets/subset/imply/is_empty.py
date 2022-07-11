from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Equal(A - B, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Subset(A, B))

    Eq << ~Eq[-1]

    Eq << sets.ne_empty.imply.any_el.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.el_complement.imply.et, simplify=None)

    Eq << sets.any_et.imply.any.single_variable.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << sets.any.imply.any.limits.swap.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(sets.el.subset.imply.el, Eq[0])

    Eq << algebra.any.imply.any_et.limits.single_variable.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-05-04
