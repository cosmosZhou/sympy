from sympy.core.relational import Equality

from axiom.utility import prove, apply

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy import LAMBDA
from sympy import Symbol
import axiom
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from axiom import sets


@apply(imply=True)
def apply(given, w=None, n=None):
    e, S = axiom.is_Contains(given)
    x, i = e.args
    
    if n is None:
        n = x.shape[0]
        
    j = Symbol.j(integer=True)
    if w is None:    
        w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap        
    k = Symbol.k(integer=True)

    return Contains(w[i, j, k] @ x[:n], S)


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(shape=(n,), integer=True)    
    
    S = Symbol.S(etype=dtype.integer)
    i = Symbol.i(integer=True)
    Eq << apply(Contains(x[i], S))
    
    i, j, k = Eq[-1].lhs.args[0].indices
    
    Eq << (Eq[0].lhs[k] @ x).this.args[0].definition

    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[2].subs(Eq[-1])
    
    Eq <<= Eq[1].subs(i, j), Eq[1].subs(i, k)
    
    Eq << sets.contains.contains.imply.contains.piecewise.apply(Eq[1], Eq[-1], Eq[-2], piecewise=Eq[-3].lhs)

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
