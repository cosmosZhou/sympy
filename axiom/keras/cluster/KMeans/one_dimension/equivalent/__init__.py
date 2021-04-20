from sympy import *
from axiom.utility import prove, apply
from axiom import keras, algebra, sets
import axiom
from axiom.keras.cluster.KMeans.one_dimension.nonoverlapping import cluster, mean


@apply
def apply(*given, x=None):
    eq_sum, eq_union = given
    w_sum, M = axiom.is_Equal(eq_sum)
    w_union, M_interval = axiom.is_Equal(eq_union)
    
    zero, _M = axiom.is_Interval(M_interval, integer=True)
    assert _M == M
    assert zero == 0
    
    wi_abs, *limits = axiom.is_Sum(w_sum)
    wi, *_limits = axiom.is_UNION(w_union)
    
    assert limits == _limits
    
    _wi = axiom.is_Abs(wi_abs)
    assert _wi == wi
    
    i = axiom.limit_is_symbol(limits)
    w, _i = axiom.is_Indexed(wi)
    assert _i == i
    
    _M = x.shape[0]
    assert _M == M
    
    j = Symbol.j(integer=True)
        
    k = w.shape[0]
    
    return Equivalent(Contains(j, w[i]) & Contains(i, Interval(0, k - 1, integer=True)), 
                      Equal(i, Sum[i](i * Bool(Contains(j, w[i])))) & Contains(j, Interval(0, M - 1, integer=True)))


@prove
def prove(Eq):
    M = Symbol.M(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    k = Symbol.k(domain=Interval(0, M - 1, integer=True))
        
    x = Symbol.x(real=True, shape=(M,))
    w = Symbol.omega(shape=(k,), etype=dtype.integer, emptyset=False)
    
    Eq << apply(Equal(Sum[i](abs(w[i])), M), Equal(UNION[i](w[i]), k.domain), x=x)


if __name__ == '__main__':
    prove()

from . import w_quote