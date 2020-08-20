
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, identity

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Multiplication
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol('w', integer=True, shape=(n, n, n), definition=Ref[i](Multiplication(n, i, lamda)))
        w_quote = Symbol("w'", integer=True, shape=(n, n, n), definition=Ref[i](Multiplication(n, i, 1 / lamda)))
    else:
        assert w[i] == Multiplication(n, i, lamda)
        assert w_quote[i] == Multiplication(n, i, 1 / lamda)
    
    return Equality(x @ w[i] @ w_quote[i] , x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    lamda = Symbol('lamda', real=True)
    Eq << apply(x, lamda)

    i, *_ = Eq[0].lhs.indices    
    
    w = Eq[0].lhs.base
    w_quote = Eq[1].lhs.base
    
    Eq << identity(x @ w[i]).subs(Eq[0])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1] @ w_quote[i]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].function.expand()
    
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
