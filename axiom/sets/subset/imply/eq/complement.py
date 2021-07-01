from util import *


@apply
def apply(given):
    A, B = given.of(Subset)

    return Equal(abs(B // A), abs(B) - abs(A))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Subset(A, B, evaluate=False))

    Eq << sets.imply.eq.principle.addition.apply(B // A, B & A)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Eq[-1].apply(algebra.is_zero.given.eq)

    Eq << sets.subset.imply.eq.intersection.apply(Eq[0])

    Eq << Eq[-1].apply(algebra.eq.imply.eq.abs)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

