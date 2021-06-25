from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(Lamda(lhs, *limits).simplify(), Lamda(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Equal(f(i), g(i)), (i,))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], Lamda[i], simplify=False)


if __name__ == '__main__':
    run()

