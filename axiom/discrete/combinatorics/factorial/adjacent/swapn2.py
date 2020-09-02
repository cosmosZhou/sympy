from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, Ref
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from axiom.discrete.combinatorics.factorial.adjacent import swap2_invariant


@plausible
def apply(n, w=None):
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
        
    x = Symbol('x', shape=(n,), integer=True, nonnegative=True)
    
    P = Symbol('P', dtype=dtype.integer * n, definition=conditionset(x, Equality(x.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[x:P](Contains(w[i, j] @ x, P))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    
    Eq << apply(n)
    
    w = Eq[0].lhs.base
    i, j = Eq[0].lhs.indices
    
    x = Eq[2].variable
    
    Eq << swap2_invariant.apply(x, w)
    
    Eq << Eq[2].definition.subs(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[1])
        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
