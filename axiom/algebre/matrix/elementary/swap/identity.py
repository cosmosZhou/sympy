from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
    
    return Equality(Ref[k:n](x[(w[i, j] @ Ref[k:n](k))[k]]), w[i, j] @ x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    Eq << apply(x)
    
    w = Eq[0].lhs.base
    i, j = Eq[0].lhs.indices
    
    k = Eq[1].lhs.variable
    
    Eq << Eq[0][k]  
    Eq << Eq[-1] @ Ref[k:n](k)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq.lhs_assertion = x[Eq[-1].lhs].this.subs(Eq[-1]).this.rhs.asKroneckerDelta().this.rhs.expand()
    
    Eq << (w[i, j] @ x).this.expand()
    
    Eq << Eq[-1][k].this.rhs.asKroneckerDelta().this.rhs.expand()
    
    Eq << Eq.lhs_assertion.subs(Eq[-1].reversed)
    
    Eq << Eq[-1].reference((k,))


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
