from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import Ref
from axiom.discrete.combinatorics.factorial.adjacent import swap2_utility, \
    swap2_utility_general
from sympy.concrete.products import MatProduct


@plausible
def apply(x, d, w=None):
    n = x.shape[0]
    m = d.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))

    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    multiplier = MatProduct[i:m](w[i, d[i]])
    return Equality(Ref[k](x[(Ref[k](k) @ multiplier)[k]]), x @ multiplier)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    m = Symbol('m', domain=Interval(2, oo, integer=True))
    x = Symbol('x', complex=True, shape=(n,))
    d = Symbol('d', integer=True, shape=(oo,))
        
    Eq << apply(x, d[:m])    
    return
    k = Eq[-1].lhs.variable
    Eq << Eq[-1][k]
    
    w = Eq[0].lhs.base
    i, j = Eq[0].lhs.indices
    d = Eq[1].rhs.args[0].indices[1].base
    
    Eq << swap2_utility.apply(x, w).subs(i, 0).subs(j, d[0])
    
    Eq << w[1, d[1]] @ Eq[-1] 
    
    Eq << Eq[1].subs(Eq[-1].reversed)
    
    Eq << swap2_utility_general.apply(x, w[0, d[0]] @ Ref[k](k), w).subs(i, 1).subs(j, d[1])


if __name__ == '__main__':
    prove(__file__)