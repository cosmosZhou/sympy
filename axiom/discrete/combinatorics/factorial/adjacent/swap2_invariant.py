from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(x):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    
    lhs = (w[i, j] @ x).set_comprehension()
    return Equality(lhs, x.set_comprehension(free_symbol=lhs.variable))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    x = Symbol('x', shape=(n,), integer=True)    
    
    Eq << apply(x)
    
#     print(Eq[1].lhs.variable._assumptions)
    k = Eq[1].lhs.variable.copy(domain=Interval(0, n - 1, integer=True))
    
    Eq << Eq[0][k]
    
    Eq << Eq[0][k] @ x
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].set
    
    Eq << Eq[-1].union_comprehension((k, 0, n - 1))

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
