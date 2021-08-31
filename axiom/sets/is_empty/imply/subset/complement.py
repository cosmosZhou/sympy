from util import *


@apply
def apply(given):
    B, A = given.of(Equal[Complement, EmptySet])
    return Subset(B, A)


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(A.etype.emptySet, B - A))
#     Eq << apply(Equal(B - A, A.etype.emptySet))

    Eq << Eq[0].apply(sets.eq.imply.eq.union, A)

    Eq << Eq[1].subs(Eq[-1])


if __name__ == '__main__':
    run()

