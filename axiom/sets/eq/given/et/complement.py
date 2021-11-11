from util import *


@apply
def apply(given):
    A, BC = given.of(Equal)
    B, C = BC.of(Union)
    return Equal(Complement(A, C), Complement(B, C)), Subset(C, A)


@prove
def prove(Eq):
    from axiom import sets

    A, B, C = Symbol(etype=dtype.integer)
    Eq << apply(Equal(A, B | C))

    Eq << sets.eq_complement.subset.imply.eq.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2021-03-31
# updated on 2021-03-31
