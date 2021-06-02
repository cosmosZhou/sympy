from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[GreaterEqual])

    return GreaterEqual(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(ForAll[i:n](GreaterEqual(f(i), g(i))))

    Eq << algebra.imply.suffice.ge.induct.sum.apply(Eq[0].function, (i, 0, n))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

