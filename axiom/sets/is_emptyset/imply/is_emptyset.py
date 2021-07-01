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

    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq.A_nonempty = ~Eq[-1]

    Eq.A_positive = Eq.A_nonempty.apply(sets.is_nonemptyset.imply.is_positive)

    Eq.AB_union_empty = Eq[0].apply(algebra.eq.imply.eq.abs)

    Eq << sets.eq.imply.eq.complement.apply(Eq[0], A)

    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << sets.imply.eq.principle.addition.apply(*Eq[-2].lhs.args)

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq.A_positive.subs(Eq[-1].reversed)

    

    

    

    

    

    

    

    


if __name__ == '__main__':
    run()