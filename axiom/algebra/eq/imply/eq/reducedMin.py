from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)

    return Equal(ReducedMin(lhs).simplify(), ReducedMin(rhs).simplify())


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    i = Symbol(domain=Range(0, n))
    f, g = Symbol(shape=(n,), real=True)
    Eq << apply(Equal(f, g))

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()
