from util import *


@apply
def apply(*given, s1=None):
    from sympy.functions.combinatorial.numbers import Stirling
    equal_sum, equal_union, all_is_positive, notcontains = given
    if not all_is_positive.is_All:
        notcontains, all_is_positive, equal_sum, equal_union = given
        
    xi, (_i, zero, k) = all_is_positive.of(All[Abs > 0])    
    x, i = xi.of(Indexed)
    
    assert i == _i
    assert zero.is_zero
    
    sgm, n = equal_sum.of(Equal)
    _xi, limit = sgm.of(Sum[Abs])
    assert _xi == xi
    assert limit == (_i, zero, k)
        
    union, interval_n = equal_union.of(Equal)
    zero, _n = interval_n.of(Range)
    assert n == _n
    assert zero.is_zero
    
    _xi, _limit = union.of(Cup)
    assert _xi == xi
    assert limit == _limit    
    
    j = Symbol.j(domain=Range(0, k))
    
    a = Symbol.a(shape=(k,), etype=dtype.integer, finite=True)
    
    if s1 is None:
        s1 = Symbol.s1(Stirling.conditionset(n - 1, k, x))
    
    return Any[a:s1, j](Equal(x[i], Piecewise(({n - 1} | a[i], Equal(i, j)), (a[i], True))))


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(Equal(Sum[i:k + 1](abs(x[i])), n + 1),
                Equal(Cup[i:k + 1](x[i]), Range(0, n + 1)),
                All[i:k + 1](abs(x[i]) > 0),
                NotContains({n}, x[:k + 1].set_comprehension()))
    return
    Eq << sets.eq.eq.imply.is_emptyset.stirling2.apply(Eq[0], Eq[1])
    
    Eq << sets.is_emptyset.imply.eq.complement.apply(Eq[-1], reverse=True)


if __name__ == '__main__':
    run()

