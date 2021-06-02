from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Greater(abs(A), 0)


@prove
def prove(Eq):
    from axiom import sets, algebra
    A = Symbol.A(etype=dtype.integer, given=True)
    inequality = Unequal(A, A.etype.emptySet, evaluate=False)

    Eq << apply(inequality)

    Eq << sets.is_nonemptyset.imply.is_nonzero.apply(Eq[0])

    Eq << algebra.is_nonzero.imply.is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()

