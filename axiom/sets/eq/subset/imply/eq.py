from util import *


@apply
def apply(subset, equal):
    if subset.is_Equal and equal.is_Subset:
        subset, equal = equal, subset

    A, B = subset.of(Subset)

    A_abs, B_abs = Card(A), Card(B)

    _A_abs, _B_abs = equal.of(Equal)
    if A_abs == _A_abs:
        assert _B_abs == B_abs
    else:
        assert _B_abs == A_abs

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Subset(A, B), Equal(Card(A), Card(B)))

    Eq << sets.imply.eq.principle.add.apply(B, A)

    Eq.union_AB = Eq[-1].subs(Eq[1])

    Eq << sets.subset.imply.subset.union.apply(Eq[0], B)

    Eq << sets.subset.imply.eq.union.apply(Eq[0])

    Eq << Eq[-1].apply(sets.eq.imply.eq.card)

    Eq << Eq.union_AB.subs(Eq[-1]).reversed

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << sets.is_zero.imply.is_empty.apply(Eq[-1])

    Eq << sets.is_empty.imply.subset.complement.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2020-07-20
# updated on 2020-07-20
