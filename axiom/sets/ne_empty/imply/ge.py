from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])

    return GreaterEqual(Card(A), 1)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol(etype=dtype.integer)

    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.ne_empty.imply.gt_zero.apply(Eq[0])

    Eq << ~Eq[1]

    Eq << Eq[-1].this.expr.solve(Eq[-1].lhs)

    Eq << algebra.any_eq.cond.imply.any.subs.apply(Eq[-1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-07-12
# updated on 2020-07-12
