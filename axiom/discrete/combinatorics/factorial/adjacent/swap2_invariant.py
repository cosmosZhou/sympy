from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval, Intersection
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import Forall, Exists
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.sets import sets


@plausible
def apply(x):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    return Equality((w[i, j] @ x).set_comprehension(), x.set_comprehension())


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    x = IndexedBase('x', (n,), integer=True)    
    
    Eq << apply(x)
    
    k = Eq[1].lhs.variable
    i, j = Eq[0].lhs.indices
    u = sets.Union({i, j}, Intersection({k}, Interval(0, n - 1, integer=True)))
    print(u & {k})
        
    Eq << Eq[0][k]
    
    Eq << Eq[0][k] @ x
    
    Eq << Eq[-1].this.rhs.expand()
    
    
    
    
    Eq << Eq[-1].subs(k, i)
    
    Eq << Eq[-2].subs(k, j)

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
