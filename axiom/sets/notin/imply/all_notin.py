from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    expr, *limits = S.of(Cup)
    return All(NotElement(e, expr).simplify(), *limits)


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(NotElement(x, Cup[k:n](A[k])))

    k = Symbol(domain=Range(n))
    Eq << Eq[0].this.rhs.apply(sets.cup.to.union.split, cond=k.set)

    Eq << sets.notin.imply.et.split.union.apply(Eq[-1], simplify=None)

    Eq << algebra.cond.imply.all.apply(Eq[-2], k)


if __name__ == '__main__':
    run()

# created on 2020-09-09
# updated on 2020-09-09
