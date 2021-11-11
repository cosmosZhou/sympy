from util import *


@apply
def apply(eq, sgm):
    X, n = eq.of(Equal[Card])
    fx, (x, _X) = sgm.of(Sum)
    assert X == _X
    (a, i), (_i, _n) = X.of(Cup[FiniteSet[Indexed], Tuple[0]])
    assert _i == i and _n == n

    return Equal(sgm, Sum[i:n](fx._subs(x, a[i])))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].set_comprehension()
    Eq << apply(Equal(Card(s), n), Sum[x:s](f(x)))

    Eq << sets.eq.imply.all_ne.apply(Eq[0])

    Eq << algebra.imply.infer.eq.sum.induct.apply(Eq[1].lhs)

    Eq << algebra.cond.infer.imply.cond.transit.apply(Eq[2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-20
# updated on 2021-03-20
