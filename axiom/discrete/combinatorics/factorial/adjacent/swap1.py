from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.matrices.expressions.matexpr import Swap


@plausible
def apply(x):
    n = x.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    w = IndexedBase('w', integer=True, shape=(n, n, n), definition=Ref[j](Swap(n, 0, j)))
    
    return Equality(x[w[j][i] @ Ref[i:n](i)], Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True)))


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))    
    x = IndexedBase('x', dtype=dtype.integer, shape=(n,))    
    
    Eq << apply(x)
    
    i = Eq[1].rhs.args[2][0].indices[0]
    Eq << Eq[0][i]

    Eq << Eq[0][i] @ Eq[1].lhs.indices[0].args[1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << identity(Eq[1].lhs).subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)
