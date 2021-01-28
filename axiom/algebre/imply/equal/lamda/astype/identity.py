from axiom.utility import prove, apply

from sympy import *

import axiom
from axiom import algebre
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply(imply=True)
def apply(lamda):
    function, *limits = axiom.is_LAMBDA(lamda)
    
    (i, zero, n_1), (j, _zero, _n_1) = axiom.limits_are_Interval(limits, integer=True)
    assert zero.is_Zero and _zero.is_Zero
    
    _i, _j = axiom.is_KroneckerDelta(function)
    assert i == _i and j == _j or i == _j and j == _i
    
    assert n_1 == _n_1
    
    n = n_1
    
    return Equality(lamda, Identity(n))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)
     
    Eq << apply(LAMBDA[j:n, i:n](KroneckerDelta(i, j)))
    
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    
    Eq << algebre.equal.given.equal.getitem.apply(Eq[0], i)


if __name__ == '__main__':
    prove(__file__)

