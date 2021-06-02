from util import *
import axiom


@apply
def apply(*given, s1=None):
    from sympy.functions.combinatorial.numbers import Stirling
    equal_sum, equal_union, all_is_positive, notcontains = given
    if not all_is_positive.is_ForAll:
        notcontains, all_is_positive, equal_sum, equal_union = given
        
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
    
    a = Symbol.a(shape=(k,), etype=dtype.integer, finite=True)
    
    if s1 is None:
        s1 = Symbol.s1(Stirling.conditionset(n - 1, k, x))
    
    return Exists[a:s1, j](Equal(x[i], Piecewise(({n - 1} | a[i], Equal(i, j)), (a[i], True))))


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    
    Eq << apply(Equal(Sum[i:k + 1](abs(x[i])), n + 1),
                Equal(Cup[i:k + 1](x[i]), Range(0, n + 1)),
                ForAll[i:k + 1](abs(x[i]) > 0),
                NotContains({n}, x[:k + 1].set_comprehension()))
    return
    Eq << sets.eq.eq.imply.is_emptyset.stirling2.apply(Eq[0], Eq[1])
    
    Eq << sets.is_emptyset.imply.eq.complement.apply(Eq[-1], reverse=True)


if __name__ == '__main__':
    run()

