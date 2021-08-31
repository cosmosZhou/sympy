from util import *


@apply
def apply(A, B):
    return LessEqual(Card(Union(A, B)), Card(A) + Card(B))


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B).reversed

    Eq << Eq[-1] + Eq[-2]


if __name__ == '__main__':
    run()

