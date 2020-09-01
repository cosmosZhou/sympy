
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible

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
        w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Addition(n, i, j, lamda)))
        w_quote = Symbol("w'", integer=True, shape=(n, n, n, n), definition=Ref[j, i](Addition(n, i, j, -lamda)))
    else:
        assert w[i, j] == Addition(n, i, j, lamda)
        assert w_quote[i, j] == Addition(n, i, j, -lamda)
    
    return Equality(x @ w[i, j] @ w_quote[i, j], x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    lamda = Symbol('lamda', real=True)
    Eq << apply(x, lamda)

    i, j = Eq[0].lhs.indices    

    w = Eq[0].lhs.base
    w_quote = Eq[1].lhs.base
    
    Eq << (x @ w[i, j]).this.subs(Eq[0])
    
    Eq << Eq[-1].this.rhs.expand()
        
    Eq << Eq[-1].this.rhs.args[1].function.asKroneckerDelta()
    
    Eq << Eq[-1].this.rhs.args[1].function.expand()
    
    Eq << (Eq[-1] @ w_quote[i, j]).this.rhs.subs(Eq[1])     
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].function.asKroneckerDelta()
    
    Eq << Eq[-1].this.rhs.args[1].function.expand()    

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
