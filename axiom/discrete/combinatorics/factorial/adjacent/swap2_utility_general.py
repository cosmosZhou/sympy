from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(x, d, w=None):
    n = x.shape[0]
    assert d.shape == (n,)
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))

    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    return Equality(Ref[k](x[w[i, j, k] @ d]), w[i, j] @ Ref[k](x[d[k]]))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    x = Symbol('x', complex=True, shape=(n,))
    d = Symbol('d', integer=True, shape=(n,))
    
    Eq << apply(x, d)        
    
    k = Eq[-1].lhs.variable
    Eq << Eq[-1][k]
    
    d = Eq[-1].rhs.args[1].function.indices[0].base
        
    Eq << (Eq[0][k] @ Ref[k](x[d[k]])).this.rhs.expand()
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << (Eq[0][k] @ d).this.rhs.expand()
    
    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[2].reference((k,))


if __name__ == '__main__':
    prove(__file__)
