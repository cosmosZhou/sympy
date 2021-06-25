from util import *


@apply
def apply(given):
    assert given.is_NotContains

    e, S = given.args
    assert S.is_Cup
    limits = S.limits

    return All(NotContains(e, S.function).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(NotContains(x, Cup[k:n](A[k])))

    k = Symbol.k(domain=Range(0, n))
    Eq << Eq[0].this.rhs.split(k.set)

    Eq << sets.notcontains.imply.et.split.union.apply(Eq[-1], simplify=None)

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq << Eq[-2].forall((k,))


if __name__ == '__main__':
    run()

