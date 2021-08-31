from util import *


@apply
def apply(given, *limits):
    fx, A = given.of(Subset)

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n, m = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex * n)
    A = Symbol(etype=dtype.complex * n)

    Eq << apply(Subset(x[i], A), (i, 0, m))

    Eq << algebra.cond.imply.all.restrict.apply(Eq[0], (i, 0, m))

    Eq << sets.all_subset.imply.subset.cup.apply(Eq[-1])


if __name__ == '__main__':
    run()

