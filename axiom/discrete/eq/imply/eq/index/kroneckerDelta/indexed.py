from util import *


@apply
def apply(given, i=None, j=None):
    (xk, (k, a, b)), n = given.of(Equal[Cup[FiniteSet], Range[0]])
    assert b - a == n

    x = Lamda[k:a:b](xk).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from axiom import algebra, sets

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

    Eq << Eq[0].apply(sets.eq.imply.eq.card)

    Eq << sets.eq.imply.all_ne.complement.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].lhs.index, j)

    Eq << Eq[-1].this.expr.reversed

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, i)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-24
