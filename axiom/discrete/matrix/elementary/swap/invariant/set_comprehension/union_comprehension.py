from sympy import *
from axiom.utility import prove, apply
from sympy.matrices.expressions.matexpr import Swap
from axiom import algebre, sets


@apply
def apply(x, w=None, right=None, free_symbol=None):
    n = x.shape[0]
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    if w is None:    
        w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap        
    
    if right:
        lhs = (x @ w[i, j]).set_comprehension(free_symbol=free_symbol)
    else:
        lhs = (w[i, j] @ x).set_comprehension(free_symbol=free_symbol)
    return Equality(lhs, x.set_comprehension(free_symbol=free_symbol))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(shape=(n,), integer=True)    
    
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices
    
    k = Eq[1].lhs.variable.copy(domain=Interval(0, n - 1, integer=True))
    
    Eq << Eq[0].lhs[k].this.definition
    
    Eq << (Eq[0].lhs[k] @ x).this.args[0].definition
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this(i, j).apply(sets.equal.imply.equal.set_comprehension, (k, 0, n))
        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
