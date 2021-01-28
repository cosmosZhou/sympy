from sympy import Symbol
from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import prove, apply

import axiom
from axiom.sets.equal.imply.equal.swap import swap
from axiom import sets, discrete, algebre


@apply(given=True)
def apply(imply, i=None, j=None):
    x, y = axiom.is_Equal(imply)
    assert len(x.shape) == 1
    
    assert x.dtype.is_set
    if i is None:
        i = Symbol.i(integer=True)
        
    if j is None:
        j = Symbol.j(integer=True)
    
    return Equality(swap[i, j](x), swap[i, j](y))


@prove
def prove(Eq): 
    n = Symbol.n(positive=True, integer=True)
    
    x = Symbol.x(shape=(n,), etype=dtype.integer)
    y = Symbol.y(shape=(n,), etype=dtype.integer)
    
    Eq << apply(Equality(x, y))
    
    (i,), (j,) = Eq[1].lhs.limits
    Eq << sets.equal.imply.equal.swap.apply(Eq[1], i, j)
    
    Eq << sets.imply.equal.swap.apply(x, i, j)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq[-1])
    
    Eq << sets.imply.equal.swap.apply(y, i, j)
    
    Eq << algebre.equal.equal.imply.equal.transit.apply(Eq[-2], Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
