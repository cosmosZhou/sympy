from util import *


@apply
def apply(A, B):
    if isinstance(B, set):
        B = FiniteSet(*B)
    return Equal(Card(A | B), Card(A - B) + Card(B))


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(A, B)

    C = Symbol(A - B)
    Eq << Equal(C & B, B.etype.emptySet, plausible=True)

    Eq << Eq[-1].subs(C.this.definition)

    Eq << sets.intersect_is_empty.imply.eq.apply(Eq[-1])

    Eq << Eq[-1].subs(C.this.definition)


if __name__ == '__main__':
    run()

# created on 2020-07-05
