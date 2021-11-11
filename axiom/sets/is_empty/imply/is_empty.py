from util import *


@apply
def apply(given, index=0):
    args = given.of(Equal[Union, EmptySet])
    A = args[index]
    emptySet = A.etype.emptySet
    return Equal(A, emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq.A_nonempty = ~Eq[-1]

    Eq.A_positive = Eq.A_nonempty.apply(sets.ne_empty.imply.gt_zero)

    Eq.AB_union_empty = Eq[0].apply(sets.eq.imply.eq.card)

    Eq << sets.eq.imply.eq.complement.apply(Eq[0], A)

    Eq << Eq[-1].apply(sets.eq.imply.eq.card)

    Eq << sets.imply.eq.principle.add.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq.A_positive.subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2021-05-13
# updated on 2021-05-13
