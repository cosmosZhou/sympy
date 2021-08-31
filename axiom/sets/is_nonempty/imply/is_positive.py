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

    Eq << sets.is_nonempty.imply.is_nonzero.apply(Eq[0])

    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()

