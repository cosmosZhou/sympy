from util import *


@apply
def apply(given, *limits):
    fx, A = given.of(Subset)

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)

    Eq << apply(Subset(x[i], A), (i, 0, m))

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (i, 0, m))

    Eq << sets.all_subset.imply.subset.cup.apply(Eq[-1])


if __name__ == '__main__':
    run()

