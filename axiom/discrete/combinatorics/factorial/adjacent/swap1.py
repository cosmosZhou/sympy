from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.matrices.expressions.matexpr import Swap


@plausible
def apply(x):
    n = x.shape[0]
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)
    
    w = IndexedBase('w', integer=True, shape=(n, n, n), definition=Ref[j:n](Swap(n, 0, j)))

    print(w.dtype)
    print(w[j].dtype)
    print(w[j][i].dtype)
    
    return Equality(Ref[i:n](x[w[j][i] @ Ref[i:n](i)]), Ref[i:n](Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True))))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    x = IndexedBase('x', dtype=dtype.integer, shape=(n,))    
    
    Eq << apply(x)


if __name__ == '__main__':
    prove(__file__)
