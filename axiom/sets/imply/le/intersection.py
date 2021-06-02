from util import *



@apply
def apply(A, B):
    return LessEqual(abs(Intersection(A, B)), abs(A))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B).reversed

    Eq << sets.imply.ge.apply(B, A)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.apply(algebra.le.simplify.terms.common)

    Eq << Eq[-1].this.apply(algebra.is_nonnegative.imply.le)


if __name__ == '__main__':
    run()

