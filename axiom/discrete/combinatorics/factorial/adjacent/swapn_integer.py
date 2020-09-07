from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, Exists, Ref
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from axiom.discrete.combinatorics.factorial.adjacent import factorization


@plausible
def apply(given):
    assert given.is_ForAll
    S = given.rhs
    n = S.element_type.shape[0]
    
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))
    x = given.variable
    
    w, i, j = given.function.lhs.args[0].args
    
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    p = Symbol('p', shape=(n,), integer=True, nonnegative=True)
    
    P = Symbol('P', dtype=dtype.integer * n, definition=conditionset(p, Equality(p.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[p:P, x:S](Contains(Ref[k:n](x[p[k]]), S), given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = Symbol('S', dtype=dtype.integer * n)    
    
    x = Symbol('x', **S.element_symbol().dtype.dict)
    
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    
    w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[j, i](Swap(n, i, j)))
    
    given = ForAll[x:S](Contains(w[i, j] @ x, S))
    
    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(given)

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
