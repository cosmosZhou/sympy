from util import *


@apply
def apply(given):
    (fx, A), *limits = given.of(All[Subset])

    return Subset(Cup(fx, *limits).simplify(), A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n, m = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex * n)
    A = Symbol(etype=dtype.complex * n)

    Eq << apply(All[i:0:m](Subset(x[i], A)))

    Eq << sets.imply.suffice.subset.induct.lhs.apply(Subset(x[i], A), (i, 0, m))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

