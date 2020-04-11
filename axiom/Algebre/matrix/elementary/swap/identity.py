
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap, Identity


@plausible
def apply(n, w=None):
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    else:
        assert w[i, j] == Swap(n, i, j)
    
    return Equality(w[i, j] @ w[i, j], Identity(n))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    Eq << apply(n)
    
    Eq << Eq[0] @ Eq[0]    


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
