from util import *


@apply
def apply(n, k=None):
    from sympy.functions.combinatorial.numbers import Stirling
    if k is None:
        k = Symbol.k(domain=Range(1, n + 1))
    assert k <= n and k > 0
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    s = Stirling.conditionset(n, k, x)
    return Unequal(s, s.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    k = Symbol.k(domain=Range(1, n + 1), given=True)
    Eq << apply(n, k=k)

    Eq << sets.is_nonemptyset.given.any.split.conditionset.apply(Eq[0])

    i = Symbol.i(integer=True)
    x, (_, k), *_ = Eq[-1].variable.args

    a = Symbol.a(Lamda[i:k](Piecewise((Range(k - 1, n), Equal(i, k - 1)), (i.set, True))))

    Eq << algebra.any.given.cond.subs.apply(Eq[-1], x[:k], a)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[-2].this.find(Indexed).definition

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[-2].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition


if __name__ == '__main__':
    run()
