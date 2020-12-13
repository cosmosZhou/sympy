from sympy.core.relational import Equality

from axiom.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy import LAMBDA
from sympy import Symbol


@plausible
def apply(x, w=None, right=None, free_symbol=None):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    if w is None:    
        w = Symbol.w(definition=LAMBDA[j:n, i:n](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap        
    
    if right:
        lhs = (x @ w[i, j]).set_comprehension(free_symbol=free_symbol)
    else:
        lhs = (w[i, j] @ x).set_comprehension(free_symbol=free_symbol)
    return Equality(lhs, x.set_comprehension(free_symbol=free_symbol))


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(shape=(n,), integer=True)    
    
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices
    
    k = Eq[1].lhs.variable.copy(domain=Interval(0, n - 1, integer=True))
    
    Eq << Eq[0][k]
    
    Eq << Eq[0][k] @ x
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].set
    
    Eq << Eq[-1].this(i, j).union_comprehension((k, 0, n - 1))

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
