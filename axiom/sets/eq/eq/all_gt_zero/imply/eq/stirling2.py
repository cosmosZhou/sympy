from util import *


@apply
def apply(equal_sum, equal_union, all_is_positive):
    (x, i), (_i, k) = all_is_positive.of(All[Card[Indexed] > 0, Tuple[0, Expr]])
    assert i == _i

    ((_x, _i), _limit), n = equal_sum.of(Equal[Sum[Card[Indexed]]])
    assert _x == x and _i == i
    assert _limit == (_i, 0, k)

    ((_x, _i), limit), _n = equal_union.of(Equal[Cup[Indexed], Range[0, Expr]])
    assert _x == x and _i == i
    assert n == _n
    assert limit == _limit

    j = Symbol(domain=Range(k))
    complement = Range(k) - {j}
    return Equal(Cup[i:complement](x[i]) - x[j], Cup[i:complement](x[i]))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    k, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(Sum[i:k](Card(x[i])), n), Equal(Cup[i:k](x[i]), Range(n)), All[i:k](Card(x[i]) > 0))

    Eq << sets.eq.eq.imply.is_empty.stirling2.apply(Eq[0], Eq[1])

    Eq << sets.intersect_is_empty.imply.eq.complement.apply(Eq[-1], reverse=True)

if __name__ == '__main__':
    run()

# created on 2021-03-28
