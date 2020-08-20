
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, identity
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Addition
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Addition(n, i, j, lamda)))
        w_quote = Symbol("w'", integer=True, shape=(n, n, n, n), definition=Ref[i, j](Addition(n, i, j, -lamda)))
    else:
        assert w[i, j] == Addition(n, i, j, lamda)
        assert w_quote[i, j] == Addition(n, i, j, -lamda)
    
    return Equality(w_quote[i, j] @ w[i, j] @ x, x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    lamda = Symbol('lamda', real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices    

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base
    
    Eq << identity(w[i, j] @ x).subs(Eq[1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True)
    
    Eq << w_quote[i, j] @ Eq[-1]    

    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True)
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
