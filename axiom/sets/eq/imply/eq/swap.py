from sympy import Symbol, Function
from sympy.core.relational import Equal
from sympy.core.symbol import dtype
from axiom.utility import prove, apply
from sympy import LAMBDA
from sympy.matrices.expressions.matexpr import Swap

import axiom
from axiom.sets.imply.eq.swap import swap



@apply
def apply(given, i=None, j=None):
    x, y = axiom.is_Equal(given)
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

    Eq << Eq[1].subs(Eq[0])
    
if __name__ == '__main__':
    prove()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
