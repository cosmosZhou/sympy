
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Multiplication


@plausible
def apply(x, lamda, w=None):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = IndexedBase('w', integer=True, shape=(n, n, n), definition=Ref[i](Multiplication(n, lamda, i)))
        w_quote = IndexedBase("w'", integer=True, shape=(n, n, n), definition=Ref[i](Multiplication(n, 1 / lamda, i)))
    else:
        assert w[i] == Multiplication(n, lamda, i)
        assert w_quote[i] == Multiplication(n, 1 / lamda, i)
    
    return Equality(w_quote[i] @ w[i] @ x, x)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    x = Symbol('x', shape=(n,), real=True)
    lamda = Symbol('lamda', real=True)
    Eq << apply(x, lamda)

    i, *_ = Eq[0].lhs.indices    

    w_quote = Eq[0].lhs.base
    w = Eq[1].lhs.base
    
    Eq << identity(w[i] @ x).subs(Eq[1])
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << w_quote[i] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].function.expand()
    
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
