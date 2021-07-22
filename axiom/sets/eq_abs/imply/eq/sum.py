from util import *


@apply
def apply(eq, sgm):
    X, n = eq.of(Equal[Abs])
    fx, (x, _X) = sgm.of(Sum)
    assert X == _X
    (a, i), (_i, _n) = X.of(Cup[FiniteSet[Indexed], Tuple[0]])
    assert _i == i and _n == n

    return Equal(sgm, Sum[i:n](fx._subs(x, a[i])))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol.n(integer=True, positive=True)
    X = Symbol.X(etype=dtype.real)
    x = Symbol.x(real=True)
    a = Symbol.a(real=True, shape=(oo,))
    f = Function.f(real=True)
    s = a[:n].set_comprehension()
    Eq << apply(Equal(abs(s), n), Sum[x:s](f(x)))

    Eq << sets.eq.imply.all_ne.apply(Eq[0])

    Eq << algebra.imply.suffice.eq.sum.induct.apply(Eq[1].lhs)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()