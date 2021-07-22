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

    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True, given=False)
    X = Symbol.X(etype=dtype.real)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    f = Function.f(real=True)
    s = a[:n].set_comprehension()
    Eq << apply(All[j:i, i:n](Unequal(a[i], a[j])), Sum[x:s](f(x)))

    Eq << algebra.imply.suffice.eq.sum.induct.apply(Eq[1].lhs)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])








if __name__ == '__main__':
    run()