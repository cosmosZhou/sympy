from util import *


@apply
def apply(given):
    A, B = given.of(Subset)

    return Equal(Card(B - A), Card(B) - Card(A))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B, evaluate=False))

    Eq << sets.imply.eq.principle.add.apply(B - A, B & A)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Eq[-1].apply(algebra.is_zero.given.eq)

    Eq << sets.subset.imply.eq.intersect.apply(Eq[0])

    Eq << Eq[-1].apply(sets.eq.imply.eq.card)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-06-26
