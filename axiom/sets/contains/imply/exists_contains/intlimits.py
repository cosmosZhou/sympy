from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from sympy import Symbol
from sympy.core.numbers import oo
from sympy import Exists
from sympy.core.containers import Tuple


@apply(imply=True)
def apply(given, *limits):
    assert given.is_Contains    
    
    for limit in limits:        
        limit = Tuple.as_setlimit(limit)
        var, *domain = limit
        assert given._has(var)
        if domain:
            domain = domain[0]
            assert domain in given.domain_defined(var) 
        
    return Exists(given, *limits)


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(Contains(x, A[k]), (k, 0, n))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]
    
    
if __name__ == '__main__':
    prove(__file__)

