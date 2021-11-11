from util import *


@apply
def apply(given):
    A, B = given.of(Equal[Intersection, EmptySet])
    return Equal(Card(Union(A, B)), Card(A) + Card(B))


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Equal(Intersection(A, B), A.etype.emptySet))

    Eq << sets.imply.eq.sum.apply(A | B).reversed

    Eq << sets.is_empty.imply.eq.bool.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.as_Plus = Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq <<= Eq.as_Plus.rhs.args[0].this.apply(algebra.sum.to.add.split, cond=A), Eq.as_Plus.rhs.args[1].this.apply(algebra.sum.to.add.split, cond=B)

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
from . import sum
from . import complement
# created on 2020-07-05
# updated on 2020-07-05
