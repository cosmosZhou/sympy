from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Unequal(abs(A), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.is_nonemptyset.imply.any_contains.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.expr.apply(sets.contains.imply.eq.union)

    Eq.any = Eq[-1].this.expr.apply(algebra.eq.imply.eq.abs)

    Eq << sets.imply.eq.principle.addition.apply(A, Eq[-1].variable.set)

    Eq << Unequal(Eq[-1].rhs, 0, plausible=True)

    Eq << algebra.eq.ne.imply.ne.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq.any.reversed

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.ne.imply.ne.transit)


if __name__ == '__main__':
    run()

