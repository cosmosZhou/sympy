from util import *


@apply
def apply(given):
    (fx, A), *limits = given.of(All[Subset])

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)
    m = Symbol.m(integer=True, positive=True)

    Eq << apply(All[i:0:m](Subset(x[i], A)))

    Eq << sets.imply.suffice.subset.induct.lhs.apply(Subset(x[i], A), (i, 0, m))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

