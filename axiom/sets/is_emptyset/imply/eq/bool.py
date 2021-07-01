from util import *


@apply
def apply(given, wrt=None):
    A, B = given.of(Equal[Intersection, EmptySet])

    if wrt is None:
        wrt = given.generate_var(**given.lhs.etype.dict)

    return Equal(Bool(Contains(wrt, A | B)), Bool(Contains(wrt, A)) + Bool(Contains(wrt, B)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equal(A & B, A.etype.emptySet))

    Eq <<= Eq[-1].rhs.args[0].this.apply(algebra.bool.to.piecewise), Eq[-1].rhs.args[1].this.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1] + Eq[-2]

    Eq << sets.is_emptyset.imply.eq.piecewise.apply(Eq[0], *Eq[-1].rhs.args)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

