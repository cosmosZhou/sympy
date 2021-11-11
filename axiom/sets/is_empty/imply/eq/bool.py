from util import *


@apply
def apply(given, wrt=None):
    A, B = given.of(Equal[Intersection, EmptySet])

    if wrt is None:
        wrt = given.generate_var(**given.lhs.etype.dict)

    return Equal(Bool(Element(wrt, A | B)), Bool(Element(wrt, A)) + Bool(Element(wrt, B)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A, B = Symbol(etype=dtype.integer)

    Eq << apply(Equal(A & B, A.etype.emptySet))

    Eq <<= Eq[-1].rhs.args[0].this.apply(algebra.bool.to.piece), Eq[-1].rhs.args[1].this.apply(algebra.bool.to.piece)

    Eq << Eq[-1] + Eq[-2]

    Eq << sets.is_empty.imply.eq.piece.apply(Eq[0], *Eq[-1].rhs.args)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[1].this.lhs.apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

# created on 2020-07-04
# updated on 2020-07-04
