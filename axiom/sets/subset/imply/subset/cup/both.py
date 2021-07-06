from util import *


@apply
def apply(given, *limits):
    lhs, rhs = given.of(Subset)

    return Subset(Cup(lhs, *limits).simplify(), Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)

    f = Function.f(shape=(), etype=dtype.real)
    g = Function.g(shape=(), etype=dtype.real)

    Eq << apply(Subset(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].apply(algebra.cond.imply.all.restrict, (i, 0, n))

    Eq << sets.all_subset.imply.subset.cup.apply(Eq[-1], simplify=False)


if __name__ == '__main__':
    run()
