from util import *


@apply
def apply(n, k):
    from sympy.functions.combinatorial.numbers import Stirling
    return Equal(Stirling(n + 1, k + 1), Stirling(n, k) + (k + 1) * Stirling(n, k + 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra
    k = Symbol.k(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n, k)

    Eq << Eq[0].apply(algebra.cond.given.et.all, cond=k < n)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    k_ = Symbol.k(domain=Range(1, n))
    Eq << discrete.combinatorics.stirling.second.recurrence.k_less_than_n.apply(n, k_)

    Eq << Eq[-1].apply(algebra.cond.imply.all.restrict, (k_,))

    Eq << algebra.all.given.et.apply(Eq[-2], cond=n.set)

    Eq << Eq[-1].this().function.simplify()


if __name__ == '__main__':
    run()

from . import k_less_than_n
