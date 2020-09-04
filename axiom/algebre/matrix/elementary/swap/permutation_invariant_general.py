from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, Ref
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from axiom.algebre.matrix import elementary
from sympy.concrete.products import MatProduct


@plausible
def apply(m, d, w=None):
    n = d.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    
    assert m >= 0
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
        
    x = Symbol('x', shape=(n,), integer=True, nonnegative=True)
    
    P = Symbol('P', dtype=dtype.integer * n, definition=conditionset(x, Equality(x.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[x:P](Contains(x @ MatProduct[i:m](w[i, d[i]]), P))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    m = Symbol('m', integer=True, nonnegative=True)
    d = Symbol('d', shape=(n,), integer=True, nonnegative=True)
    
    Eq << apply(m, d)
    
    Eq << Eq[-1].subs(m, 0)
    
    Eq << Eq[-1].subs(m, m + 1)
    
    w, i, j = Eq[0].lhs.args
    
    Eq << elementary.swap.permutation_invariant.apply(n, w, left=False).subs(i, m).subs(j, d[m])
    
    Eq << Eq[-1].subs(Eq[-1].variable, Eq[2].function.lhs)
    
    Eq << Eq[-1].this.args[0].lhs.simplify()
    
    Eq << Eq[-1].forall(*Eq[-3].limits[0])
    
    Eq << (Eq[-1] & Eq[2])
    
    Eq << Eq[-1].split()

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
