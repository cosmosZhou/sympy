from util import *


@apply
def apply(eq, sgm, *, simplify=True):
    X, n = eq.of(Equal[Card])
    fx, (x, S[X]) = sgm.of(Sum)
    (a, i), (S[i], S[0], S[n]) = X.of(Cup[FiniteSet[Indexed]])
    assert not fx.shape
    if fx._has(i):
        i = sgm.generate_var({i}, integer=True)
    lamda = Lamda[i:n](fx._subs(x, a[i]))
    if simplify:
        lamda = lamda.simplify()
    return Equal(sgm, ReducedSum(lamda))


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    s = a[:n].cup_finiteset()
    Eq << apply(Equal(Card(s), n), Sum[x:s](f(x)))

    Eq << sets.eq_card.imply.eq.sum.apply(Eq[0], Eq[1].find(Sum))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.reducedSum)

    


if __name__ == '__main__':
    run()
# created on 2022-01-10
