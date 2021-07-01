from util import *


@apply
def apply(given):
    A, BC = given.of(Equal)
    B, C = BC.of(Union)
    return Equal(Complement(A, C), Complement(B, C)), Subset(C, A)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)
    Eq << apply(Equal(A, B | C))

    Eq << sets.eq_complement.subset.imply.eq.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()

