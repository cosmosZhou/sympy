from util import *


import axiom


@apply
def apply(*given):
    equal_sum, equal_union, all_is_positive = given
    if not all_is_positive.is_ForAll:
        all_is_positive, equal_sum, equal_union = given

    abs_xi, *limits = axiom.all_is_positive(all_is_positive)

    xi = abs_xi.of(Abs)
    x, i = xi.of(Indexed)

    _i, zero, k = axiom.limit_is_Interval(limits, integer=True)
    assert i == _i
    assert zero.is_zero

    sgm, n = equal_sum.of(Equal)
    _abs_xi, *_limits = sgm.of(Sum)
    assert abs_xi == _abs_xi
    assert limits == _limits

    union, interval_n = equal_union.of(Equal)
    zero, _n = interval_n.of(Range)
    assert n == _n
    assert zero.is_zero

    _xi, *_limits = union.of(Cup)
    assert _xi == xi
    assert limits == _limits

    j = Symbol.j(domain=Range(0, k))
    complement = Range(0, k) // {j}
    return Equal(Cup[i:complement](x[i]) // x[j], Cup[i:complement](x[i]))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(Equal(Sum[i:k](abs(x[i])), n), Equal(Cup[i:k](x[i]), Range(0, n)), ForAll[i:k](abs(x[i]) > 0))

    Eq << sets.eq.eq.imply.is_emptyset.stirling2.apply(Eq[0], Eq[1])

    Eq << sets.is_emptyset.imply.eq.complement.apply(Eq[-1], reverse=True)

if __name__ == '__main__':
    run()

