from util import *


@apply
def apply(eq, eq_abs, sgm):
    ((a, i), (_i, n)), X = eq.of(Equal[Cup[FiniteSet[Indexed], Tuple[0]]])
    assert _i == i

    _X, _n = eq_abs.of(Equal[Card])
    fx, (x, __X) = sgm.of(Sum)
    assert X == _X == __X

    return Equal(sgm, Sum[i:n](fx._subs(x, a[i])))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    X = Symbol(etype=dtype.real)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    Eq << apply(Equal(X, a[:n].set_comprehension()), Equal(Card(X), n), Sum[x:X](f(x)))

    Eq << Eq[1].subs(Eq[0])

    fx, (x, X) = Eq[2].lhs.of(Sum)
    Eq << sets.eq_card.imply.eq.sum.apply(Eq[-1], Sum[x:Eq[-1].lhs.arg](fx))
    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2021-03-21
# updated on 2021-03-21
