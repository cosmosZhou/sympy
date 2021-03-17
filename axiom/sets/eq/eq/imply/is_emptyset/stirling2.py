from sympy import *
from axiom.utility import prove, apply

from axiom import sets, algebre
import axiom


@apply
def apply(*given):
    equal_sum, equal_union = given
    
    sgm, n = axiom.is_Equal(equal_sum)
    abs_xi, *limits = axiom.is_Sum(sgm)
    xi = axiom.is_Abs(abs_xi)
    x, i = axiom.is_Indexed(xi)
    
    _i, zero, k = axiom.limit_is_Interval(limits, integer=True)
    assert _i == i
    assert zero.is_zero
            
    union, interval_n = axiom.is_Equal(equal_union)
    zero, _n = axiom.is_Interval(interval_n, integer=True)
    assert n == _n
    assert zero.is_zero
    
    _xi, *_limits = axiom.is_UNION(union)
    assert _xi == xi
    assert limits == _limits    

    j = Symbol.j(domain=Interval(0, k - 1, integer=True))    
    complement = Interval(0, k - 1, integer=True) // {j}
    
    return Equality(UNION[i:complement](x[i]) & x[j], xi.etype.emptySet)


@prove
def prove(Eq):
    x = Symbol.x(shape=(oo,), etype=dtype.integer, finite=True)
    k = Symbol.k(integer=True, positive=True)
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(Equal(Sum[i:k](abs(x[i])), n), Equal(UNION[i:k](x[i]), Interval(0, n - 1, integer=True)))

    Eq << algebre.eq.imply.eq.abs.apply(Eq[1])
    
    Eq << algebre.eq.eq.imply.eq.transit.apply(Eq[-1], Eq[0])
    
    Eq << sets.eq.imply.forall_is_emptyset.apply(Eq[-1])
    
    j = Eq[2].lhs.args[0].index
    Eq << Eq[-1].limits_subs(i, j)
    
    Eq << Eq[-1].limits_subs(Eq[-1].variable, i)
    
    Eq << sets.forall_eq.imply.eq.union.apply(Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

