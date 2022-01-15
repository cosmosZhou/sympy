from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Subset)
    assert lhs.is_Cup
    return All(Subset(lhs.expr, rhs).simplify(), *lhs.limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex * n)
    A = Symbol(etype=dtype.complex * n)
    Eq << apply(Subset(Cup[i:n](x[i]), A))

    k = Symbol(domain=Range(n))
    Eq << Eq[0].this.lhs.apply(sets.cup.to.union.split, cond=k.set)

    Eq << sets.subset.imply.subset.split.union.apply(Eq[-1])

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (k,))


if __name__ == '__main__':
    run()

# created on 2020-07-28
