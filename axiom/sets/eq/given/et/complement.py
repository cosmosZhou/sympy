from util import *
import axiom

# given : A & B = A | B => A = B


@apply
def apply(given):
    A, BC = given.of(Equal)
    B, C = BC.of(Union)
    return Equal(Complement(A, C), Complement(B, C)) & Subset(C, A)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    C = Symbol.C(etype=dtype.integer)

    Eq << apply(Equal(A, B | C))

    Eq << Eq[1].apply(sets.subset.eq.imply.eq.split.complement)



if __name__ == '__main__':
    run()
