from util import *


@apply
def apply(given):
    assert given.is_Equal
    lhs, rhs = given.args
    if rhs.is_EmptySet:
        assert lhs.is_Intersection
        A, B = lhs.args
    else:
        assert lhs.is_EmptySet
        assert rhs.is_Intersection
        A, B = rhs.args

    return Equal(abs(Union(A, B)), abs(A) + abs(B))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equal(Intersection(A, B), A.etype.emptySet))

    Eq << sets.imply.eq.sum.apply(A | B).reversed

    Eq << sets.is_emptyset.imply.eq.bool.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.as_Plus = Eq[-1].this.rhs.astype(Add)

    Eq <<= Eq.as_Plus.rhs.args[0].this.split(A), Eq.as_Plus.rhs.args[1].this.split(B)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1] + Eq.as_Plus

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq << sets.imply.eq.sum.apply(A)

    Eq << sets.imply.eq.sum.apply(B)

    Eq << Eq[-1] + Eq[-2] + Eq[-3]

    Eq << Eq[-1].this.apply(algebra.eq.simplify.terms.common)


if __name__ == '__main__':
    run()

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml
