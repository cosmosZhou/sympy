from util import *

from axiom.discrete.eq.imply.et.index import index_function


@apply
def apply(given, j=None):
    assert given.is_Equal
    x_cup_finiteset, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_cup_finiteset.limits) == 1
    k, a, b = x_cup_finiteset.limits[0]
    assert b - a == n
    x = Lamda(x_cup_finiteset.expr.arg, *x_cup_finiteset.limits).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    assert j >= 0 and j < n

    index = index_function(n)

    return Equal(index[x[j]](x[:n]), j)


@prove
def prove(Eq):
    from axiom import discrete, sets, algebra
    n = Symbol(domain=Range(2, oo), given=True)

    x = Symbol(shape=(oo,), integer=True, given=True)

    k = Symbol(integer=True)

    j = Symbol(domain=Range(n), given=True)

    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), j)

    t, i = Symbol(domain=Range(n))

    Eq << discrete.eq.imply.et.index.apply(Eq[0], j=t)

    Eq.ou = algebra.cond.imply.ou.subs.apply(Eq[-1], t, x[j])

    Eq.equality = Eq.ou.args[0].copy(plausible=True)

    Eq.xj_notcontains = Eq.ou.args[1].copy(plausible=True)

    Eq << sets.eq.imply.subset.apply(Eq[0])

    Eq << sets.subset_cup.imply.all_subset.apply(Eq[-1])

    Eq << algebra.all.imply.cond.subs.apply(Eq[-1], Eq[-1].variable, j)

    Eq <<= Eq[-1] & Eq.xj_notcontains

    Eq << discrete.eq.imply.eq.index.kroneckerDelta.indexed.apply(Eq[0], i, j)

    Eq.ou1 = algebra.cond.imply.ou.subs.apply(Eq[-1], i, Eq[1].lhs)

    Eq.ou2 = algebra.cond.imply.ou.subs.apply(Eq[2], t, x[j])

    Eq.index_contains = Eq.ou2.args[0].copy(plausible=True)

    Eq <<= Eq.ou & ~Eq.xj_notcontains

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)

    Eq <<= Eq.ou2 & ~Eq.xj_notcontains

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=0)

    Eq <<= Eq.ou1 & Eq.index_contains

    Eq << algebra.et.imply.cond.apply(Eq[-1], index=1)

    Eq << Eq[-1].subs(Eq.equality)

    Eq << Eq[-1].this.apply(algebra.eq.simplify.kroneckerDelta)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-10-25
