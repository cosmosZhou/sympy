from util import *


@apply
def apply(given):
    A = given.of(Equal[0])
    A = A.of(Abs)

    return Equal(A, A.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equal(abs(A), 0))

    Eq << ~Eq[-1]

    Eq << sets.is_nonemptyset.imply.is_nonzero.apply(Eq[-1])

    Eq << ~Eq[0]


if __name__ == '__main__':
    run()

