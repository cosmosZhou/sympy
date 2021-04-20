from sympy import *

from axiom.utility import prove, apply
import axiom
from axiom import sets


@apply
def apply(given):
    x, S = axiom.is_Contains(given)
    function, *limits = axiom.is_UNION(S)    

    for v in S.variables:
        if x._has(v):
            _v = v.generate_free_symbol(given.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Contains(x, S.function).simplify()
    return Exists(contains, *S.limits)


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    k = Symbol.k(integer=True)
    
    A = Symbol.A(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Contains(x, UNION[k:n](A[k])))
    
    Eq << ~Eq[1]
    
    Eq << sets.forall_notcontains.imply.notcontains.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    
    
if __name__ == '__main__':
    prove()

