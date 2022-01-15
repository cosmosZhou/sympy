from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Greater(Card(A), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << sets.ne_empty.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.imply.gt_zero.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-12
