
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol
from sympy.utility import check, plausible, Ref, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(w):
    n = w.shape[0]
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    assert len(w.shape) == 4 and all(s == n for s in w.shape)
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap 
    
    return Equality(w[i, j], w[j, i])


@check
def prove(Eq):
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    Eq << apply(w)
    
    Eq << Equality.by_definition_of(w[j, i])
    
    Eq << Eq[0] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.rhs.function.asKroneckerDelta()
    
    Eq.expand = Eq[-1].this.rhs.function.expand()
    
    (l, *_), (m, *_) = Eq[-1].rhs.limits     
    Eq << Equality(KroneckerDelta(i, l) * KroneckerDelta(i, m), KroneckerDelta(i, l) * KroneckerDelta(l, m), plausible=True).equivalent
    Eq << Equality(KroneckerDelta(j, l) * KroneckerDelta(j, m), KroneckerDelta(j, l) * KroneckerDelta(l, m), plausible=True).equivalent
    Eq << Equality(KroneckerDelta(i, j) * KroneckerDelta(j, l), KroneckerDelta(i, j) * KroneckerDelta(i, l), plausible=True).equivalent    
    Eq.expand = Eq.expand.subs(Eq[-1], Eq[-2], Eq[-3])

    Eq.expand = Eq.expand.this.rhs.function.collect(KroneckerDelta(l, m))
    
    Eq << Equality(Eq.expand.rhs.function.args[1], 1, plausible=True)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
