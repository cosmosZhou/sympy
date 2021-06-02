from util import *
import axiom


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Equal)

    return Equal(MIN(lhs, *limits).simplify(), MIN(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << algebra.eq.imply.eq.invoke.apply(Eq[0], MIN[i:n], simplify=False)


if __name__ == '__main__':
    run()

