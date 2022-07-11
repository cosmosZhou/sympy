from util import *


@apply
def apply(all_ne, sgm):
    (ai, aj), (j, S[0], i_), (i, S[0], n) = all_ne.of(All[Unequal])
    if ai._has(j):
        ai, xj = aj, ai

    assert i == i_
    assert ai._subs(i, j) == aj

    fx, (x, X) = sgm.of(Sum)

    _ai, (_i, S[0], n) = X.of(Cup[FiniteSet])
    assert _ai._subs(_i, i) == ai

    return Equal(sgm, Sum[i:n](fx._subs(x, ai)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    X = Symbol(etype=dtype.real)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].cup_finiteset()
    Eq << apply(All[j:i, i:n](Unequal(a[i], a[j])), Sum[x:s](f(x)))

    Eq << algebra.imply.infer.eq.sum.induct.apply(Eq[1].lhs)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-02-05
