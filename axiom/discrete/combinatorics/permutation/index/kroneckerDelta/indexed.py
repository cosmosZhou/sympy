from util import *


@apply
def apply(given, i=None, j=None):
    (xk, (k, a, b)), n = given.of(Equal[Cup[FiniteSet], Range[0]])
    assert b - a == n

    x = Lamda[k:a:b](xk).simplify()

    if j is None:
        j = Symbol.j(domain=Range(0, n), given=True)

    if i is None:
        i = Symbol.i(domain=Range(0, n), given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol.n(domain=Range(2, oo))
    x = Symbol.x(shape=(n,), integer=True, given=True)
    k = Symbol.k(integer=True)
    j = Symbol.j(domain=Range(0, n), given=True)
    i = Symbol.i(domain=Range(0, n), given=True)
    Eq << apply(Equal(x[:n].set_comprehension(k), Range(0, n)), i, j)

    Eq << Eq[-1].apply(algebra.cond.given.et.ou, cond=Equal(i, j))

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.imply.ne.subs)

    Eq << Eq[-1].this.apply(algebra.cond.cond.imply.et, algebra.ne.cond.imply.cond)

    Eq << Eq[0].apply(algebra.eq.imply.eq.abs)

    Eq << sets.eq.imply.all_ne.complement.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].lhs.index, j)

    Eq << Eq[-1].this.function.reversed

    Eq << algebra.all.imply.ou.subs.apply(Eq[-1], Eq[-1].variable, i)

    Eq << Eq[-1].this.find(NotContains).simplify()

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
