from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Subset)
    assert lhs.is_Cup
    return ForAll(Subset(lhs.function, rhs).simplify(), *lhs.limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    x = Symbol.x(shape=(oo,), etype=dtype.complex * n)
    A = Symbol.A(etype=dtype.complex * n)

    Eq << apply(Subset(Cup[i:n](x[i]), A))

    k = Symbol.k(domain=Range(0, n))
    Eq << Eq[0].this.lhs.split(k.set)

    Eq << sets.subset.imply.subset.split.union.apply(Eq[-1])

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (k,))


if __name__ == '__main__':
    run()

