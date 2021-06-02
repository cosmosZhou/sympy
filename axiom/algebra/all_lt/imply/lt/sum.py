from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(ForAll[Less])

    return Less(Sum(lhs, *limits).simplify(), Sum(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)

    Eq << apply(ForAll[i:n](f(i) < g(i)))

    Eq << Eq[0].reversed

    Eq << algebra.all_gt.imply.gt.sum.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

