from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.expr_with_limits import Forall
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.factorial.adjacent import swap1_utility, \
    swap2_equality
import axiom


@plausible
def apply(given):
    assert given.is_Forall and len(given.limits) == 1
    x, S = given.limits[0]
    
    contains = given.function
    assert contains.is_Contains
    
    w = contains.lhs.args[0].base
    _, j = contains.lhs.args[0].indices
    i = Symbol('i', integer=True)
    
    return Forall(Contains(w[i, j] @ x, S), (x, S), given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = Symbol('S', dtype=dtype.integer * n)    
    
    x = IndexedBase('x', **S.element_symbol().dtype.dict)
    
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)    
    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i:n, j:n](Swap(n, i, j)))
    
    given = Forall(Contains(w[0, j] @ x, S), (x, S))
    
    Eq << apply(given)
    
    Eq.given_i = given.subs(j, i)    
    
    Eq << given.subs(x, Eq.given_i.function.lhs)
    
    Eq << (Eq.given_i & Eq[-1]).split()[-1]
    
    Eq << Eq.given_i.subs(x, Eq[-1].function.lhs)
    
    Eq.final_statement = (Eq[-2] & Eq[-1]).split()[0]
    
    Eq << swap2_equality.apply(n, w)
    
    Eq << Eq[-1] @ x
    
    Eq << Eq[-1].forall(Eq[-1].limits[0].args[1].args[1].arg)
    
    Eq << Eq.final_statement.subs(Eq[-1])
    
    plausible = Forall(Contains(w[i, j] @ x, S), (x, S), (j, Interval(1, n - 1, integer=True)), plausible=True)
    Eq << plausible
    
    Eq << plausible.bisect(wrt=j, domain=i.set)
    
    Eq << Eq[-1].split()
    
    as_Piecewise


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
