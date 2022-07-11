from util import *


@apply
def apply(given):
    (xi, (i, zero, n)), _n = given.of(Equal[Card[Cup[FiniteSet]]])
    assert zero == 0
    assert n == _n

    j = xi.generate_var(integer=True)
    xj = xi.subs(i, j)

    return All[j:i, i:n](Unequal(xi, xj))


@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True, given=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True, given=True)
    Eq << apply(Equal(Card(x[:n].cup_finiteset()), n))

    xi = Eq[1].expr.args[0]
    x, i = xi.args
    b = Symbol(Lamda[i:n](x[i].set))
    Eq << Card(Cup[i:n](b[i])).this.arg.expr.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])

    Eq << Sum[i:n](Card(b[i])).this.expr.arg.definition

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])

    Eq << sets.eq.imply.all_is_empty.apply(Eq[-1])

    Eq << Eq[-1].this.find(Indexed).definition

    Eq << Eq[-1].this.find(Indexed).definition


if __name__ == '__main__':
    run()

from . import complement
# created on 2021-03-20
