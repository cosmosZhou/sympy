from util import *

from axiom.keras.cluster.KMeans.nonoverlapping import cluster, mean


@apply
def apply(*given, x=None):
    eq_sum, eq_union = given
    w_sum, M = eq_sum.of(Equal)
    w_union, M_interval = eq_union.of(Equal)
    
    zero, _M = M_interval.of(Range)
    assert _M == M
    assert zero == 0
    
    wi_abs, limit = w_sum.of(Sum)
    wi, _limit = w_union.of(Cup)
    
    assert limit == _limit
    
    _wi = wi_abs.of(Abs)
    assert _wi == wi
    
    (i,) = limit
    w, _i = wi.of(Indexed)
    assert _i == i
    
    _M = x.shape[0]
    assert _M == M
    
    j = Symbol.j(integer=True)
        
    k = w.shape[0]
    
    return Equivalent(Contains(j, w[i]) & Contains(i, Range(0, k)),
                      Equal(i, Sum[i](i * Bool(Contains(j, w[i])))) & Contains(j, Range(0, M)))


@prove(proved=False)
def prove(Eq):
    M = Symbol.M(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    
    k = Symbol.k(domain=Range(0, M))
        
    x = Symbol.x(real=True, shape=(M, n))
    w = Symbol.omega(shape=(k,), etype=dtype.integer, emptyset=False)
    
    Eq << apply(Equal(Sum[i](abs(w[i])), M), Equal(Cup[i](w[i]), k.domain), x=x)


if __name__ == '__main__':
    run()

from . import w_quote
