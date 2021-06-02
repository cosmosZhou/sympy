from util import *


@apply
def apply(*given):
    import axiom
    equal_sum, equal_union = given

    sgm, n = equal_sum.of(Equal)
    abs_xi, *limits = sgm.of(Sum)
    xi = abs_xi.of(Abs)
    x, i = xi.of(Indexed)

    _i, zero, k = axiom.limit_is_Interval(limits, integer=True)
    assert _i == i
    assert zero.is_zero

    union, interval_n = equal_union.of(Equal)
    zero, _n = interval_n.of(Range)
    assert n == _n
    assert zero.is_zero

    _xi, *_limits = union.of(Cup)
    assert _xi == xi
    assert limits == _limits

    j = Symbol.j(domain=Range(0, k))
    complement = Range(0, k) // {j}

    return Equal(Cup[i:complement](x[i]) & x[j], xi.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(Equal(Sum[i:k](abs(x[i])), n), Equal(Cup[i:k](x[i]), Range(0, n)))

    Eq << algebra.eq.imply.eq.abs.apply(Eq[1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[0])

    Eq << sets.eq.imply.all_is_emptyset.complement.apply(Eq[-1])

    j = Eq[2].lhs.args[0].index
    Eq << Eq[-1].limits_subs(i, j)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, i)

    Eq << sets.all_eq.imply.eq.union.apply(Eq[-1])


if __name__ == '__main__':
    run()

