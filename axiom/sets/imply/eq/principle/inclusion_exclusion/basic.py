from util import *


@apply
def apply(A, B):
    return Equal(abs(A | B), abs(A) + abs(B) - abs(A & B))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.eq.principle.addition.apply(B, A)

    Eq << Eq[-1].reversed + Eq[-2]

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << Eq[-1] - Eq[-1].rhs.args[1]

    Eq << sets.imply.eq.principle.addition.apply(B // A, A & B).reversed


if __name__ == '__main__':
    run()

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
