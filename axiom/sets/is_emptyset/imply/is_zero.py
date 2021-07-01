from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    return Equal(abs(A), 0)


@prove
def prove(Eq):
    from axiom import algebra

    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(Equal(A, A.etype.emptySet))

    Eq << algebra.eq.imply.eq.abs.apply(Eq[0])


if __name__ == '__main__':
    run()

