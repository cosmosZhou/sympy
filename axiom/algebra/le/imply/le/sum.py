from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(LessEqual)

    return LessEqual(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(LessEqual(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq << algebra.all_le.imply.le.sum.apply(Eq[-1])


if __name__ == '__main__':
    run()
