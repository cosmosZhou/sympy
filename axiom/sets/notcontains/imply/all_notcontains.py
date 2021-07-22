from util import *


@apply
def apply(given):
    e, S = given.of(NotContains)
    expr, *limits = S.of(Cup)
    return All(NotContains(e, expr).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    A = Symbol.A(shape=(oo,), etype=dtype.integer)
    Eq << apply(NotContains(x, Cup[k:n](A[k])))

    k = Symbol.k(domain=Range(0, n))
    Eq << Eq[0].this.rhs.apply(sets.cup.to.union.split, cond=k.set)

    Eq << sets.notcontains.imply.et.split.union.apply(Eq[-1], simplify=None)

    Eq << algebra.cond.imply.all.apply(Eq[-2], k)


if __name__ == '__main__':
    run()

