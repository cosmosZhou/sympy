from util import *


@apply
def apply(given):
    (fx, A), *limits = given.of(ForAll[Subset])

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)

    Eq << apply(ForAll[i:0:m](Subset(x[i], A)))

    Eq << sets.subset.imply.all_subset.split.cup.apply(Eq[1])


if __name__ == '__main__':
    run()

