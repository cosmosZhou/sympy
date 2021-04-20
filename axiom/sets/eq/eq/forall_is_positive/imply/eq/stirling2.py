from sympy import *
from axiom.utility import prove, apply

from axiom import sets, algebra
import axiom


@apply
def apply(*given):
    equal_sum, equal_union, forall_is_positive = given
    if not forall_is_positive.is_ForAll:
        forall_is_positive, equal_sum, equal_union = given
        
    abs_xi, *limits = axiom.forall_is_positive(forall_is_positive)
    
    xi = axiom.is_Abs(abs_xi)    
    x, i = axiom.is_Indexed(xi)
    
    _i, zero, k = axiom.limit_is_Interval(limits, integer=True)
    assert i == _i
    assert zero.is_zero
    
    sgm, n = axiom.is_Equal(equal_sum)
    _abs_xi, *_limits = axiom.is_Sum(sgm)
    assert abs_xi == _abs_xi
    assert limits == _limits
        
    union, interval_n = axiom.is_Equal(equal_union)
    zero, _n = axiom.is_Interval(interval_n, integer=True)
    assert n == _n
    assert zero.is_zero
    
    _xi, *_limits = axiom.is_UNION(union)
    assert _xi == xi
    assert limits == _limits    
    
    j = Symbol.j(domain=Interval(0, k - 1, integer=True))
    complement = Interval(0, k - 1, integer=True) // {j}
    return Equal(UNION[i:complement](x[i]) // x[j], UNION[i:complement](x[i]))


@prove
def prove(Eq):
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(Equal(Sum[i:k](abs(x[i])), n), Equal(UNION[i:k](x[i]), Interval(0, n - 1, integer=True)), ForAll[i:k](abs(x[i]) > 0))

    Eq << sets.eq.eq.imply.is_emptyset.stirling2.apply(Eq[0], Eq[1])
    
    Eq << sets.is_emptyset.imply.eq.complement.apply(Eq[-1], reverse=True)

if __name__ == '__main__':
    prove()

