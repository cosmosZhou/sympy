from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])

    return GreaterEqual(abs(A), 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.is_nonemptyset.imply.is_positive.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << Eq[-1].this.expr.solve(Eq[-1].lhs)

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-1], Eq[2])


if __name__ == '__main__':
    run()

