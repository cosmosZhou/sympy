from util import *


@apply
def apply(*given):
    equal_sum, equal_union, all_is_positive = given
    if not all_is_positive.is_All:
        all_is_positive, equal_sum, equal_union = given

    (x, i), (_i, k) = all_is_positive.of(All[Abs[Indexed] > 0, Tuple[0, Expr]])
    assert i == _i

    ((_x, _i), _limit), n = equal_sum.of(Equal[Sum[Abs[Indexed]]])
    assert _x == x and _i == i
    assert _limit == (_i, 0, k)

    ((_x, _i), limit), _n = equal_union.of(Equal[Cup[Indexed], Range[0, Expr]])
    assert _x == x and _i == i
    assert n == _n
    assert limit == _limit

    j = Symbol.j(domain=Range(0, k))
    complement = Range(0, k) - {j}
    return Equal(Cup[i:complement](x[i]) - x[j], Cup[i:complement](x[i]))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(Equal(Sum[i:k](abs(x[i])), n), Equal(Cup[i:k](x[i]), Range(0, n)), All[i:k](abs(x[i]) > 0))

    Eq << sets.eq.eq.imply.is_emptyset.stirling2.apply(Eq[0], Eq[1])

    Eq << sets.is_emptyset.imply.eq.complement.apply(Eq[-1], reverse=True)

if __name__ == '__main__':
    run()

