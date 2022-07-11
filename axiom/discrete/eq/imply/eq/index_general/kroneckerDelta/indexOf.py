from util import *


@apply
def apply(given, i=None, j=None):
    from axiom.discrete.eq.imply.et.index import index_function
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

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n

    index = index_function(n)

    di = index[i](x[:n])
    dj = index[j](x[:n])

    return Equal(KroneckerDelta(di, dj), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), i, j)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=Equal(i, j))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.imply.ne.subs)

    Eq << Eq[-1].this.apply(algebra.ne.cond.imply.cond.subs, ret=0)

    Eq << discrete.eq.imply.et.index.apply(Eq[0], j=j)[1]

    Eq << Eq[-2].this.args[0].rhs.subs(Eq[-1].reversed)

    Eq << discrete.eq.imply.et.index.apply(Eq[0], j=i)[1]

    Eq << Eq[-2].this.args[0].lhs.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(algebra.eq.ne.imply.ne.subs)


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-27
