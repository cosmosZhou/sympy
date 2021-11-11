from util import *


@apply
def apply(A, B):
    return Equal(Card(A | B), Card(A) + Card(B) - Card(A & B))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.eq.principle.add.apply(B, A)

    Eq << Eq[-1].reversed + Eq[-2]

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Eq[-1] - Eq[-1].rhs.args[1]

    Eq << sets.imply.eq.principle.add.apply(B - A, A & B).reversed


if __name__ == '__main__':
    run()

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
# created on 2020-07-06
# updated on 2020-07-06
