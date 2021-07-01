from util import *


@apply
def apply(A, B):
    return LessEqual(abs(Union(A, B)), abs(A) + abs(B))


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)

    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B).reversed

    Eq << Eq[-1] + Eq[-2]


if __name__ == '__main__':
    run()

