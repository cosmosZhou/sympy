from util import *


@apply
def apply(all_ne, sgm):
    (ai, aj), (j, _zero, i_), (i, zero, n) = all_ne.of(All[Unequal])
    if ai._has(j):
        ai, xj = aj, ai

    assert zero == _zero == 0
    assert i == i_
    assert ai._subs(i, j) == aj

    fx, (x, X) = sgm.of(Sum)

    _ai, (_i, n) = X.of(Cup[FiniteSet, Tuple[0]])
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
    s = a[:n].set_comprehension()
    Eq << apply(All[j:i, i:n](Unequal(a[i], a[j])), Sum[x:s](f(x)))

    Eq << algebra.imply.infer.eq.sum.induct.apply(Eq[1].lhs)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[0], Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-02-05
# updated on 2019-02-05