from util import *


@apply
def apply(equal_sum, equal_union):
    (xi, (_i, k)), n = equal_sum.of(Equal[Sum[Card, Tuple[0, Expr]]])
    x, i = xi.of(Indexed)

    assert _i == i

    (_xi, limit), _n = equal_union.of(Equal[Cup, Range[0, Expr]])
    assert n == _n

    assert _xi == xi
    assert limit == (_i, 0, k)

    j = Symbol(domain=Range(0, k))
    complement = Range(0, k) - {j}

    return Equal(Cup[i:complement](x[i]) & x[j], xi.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    k, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(Sum[i:k](Card(x[i])), n), Equal(Cup[i:k](x[i]), Range(0, n)))

    Eq << sets.eq.imply.eq.card.apply(Eq[1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[0])

    Eq << sets.eq.imply.all_is_empty.complement.apply(Eq[-1])

    j = Eq[2].lhs.args[0].index
    Eq << Eq[-1].limits_subs(i, j)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, i)

    Eq << sets.all_eq.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    run()

