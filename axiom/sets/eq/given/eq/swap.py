from sympy import Symbol
from sympy.core.relational import Equal
from sympy.core.symbol import dtype
from axiom.utility import prove, apply

import axiom
from axiom.sets.eq.imply.eq.swap import swap
from axiom import sets, discrete, algebra


@apply
def apply(imply, i=None, j=None):
    x, y = axiom.is_Equal(imply)
    assert len(x.shape) == 1
    
    assert x.dtype.is_set
    if i is None:
        i = Symbol.i(integer=True)
        
    if j is None:
        j = Symbol.j(integer=True)
    
    return Equal(swap[i, j](x), swap[i, j](y))


@prove
def prove(Eq): 
    n = Symbol.n(positive=True, integer=True)
    
    x = Symbol.x(shape=(n,), etype=dtype.integer)
    y = Symbol.y(shape=(n,), etype=dtype.integer)
    
    Eq << apply(Equal(x, y))
    
    (i,), (j,) = Eq[1].lhs.limits
    Eq << sets.eq.imply.eq.swap.apply(Eq[1], i, j)
    
    Eq << sets.imply.eq.swap.apply(x, i, j)
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])
    
    Eq << sets.imply.eq.swap.apply(y, i, j)
    
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])
    
if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
