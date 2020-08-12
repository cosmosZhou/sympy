
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Shift


@plausible
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Shift(n, i, j)))
    else:
        assert w[i, j] == Shift(n, i, j)
    
    return Equality(w[i, j].T @ w[i, j] @ x, x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    Eq << apply(x)
    
    Eq << Eq[0].T
    
    i, j = Eq[0].lhs.indices    

    w = Eq[0].lhs.base
    
    Eq << identity(w[i, j] @ x).subs(Eq[0])
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=i)
    
    Eq << w[i, j].T @ Eq[-1]
     
    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=i)
        

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
