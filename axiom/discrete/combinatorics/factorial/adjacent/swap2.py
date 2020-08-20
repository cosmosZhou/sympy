from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, Ref
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.factorial.adjacent import swap2_equality
import axiom


@plausible
def apply(given):
    assert given.is_ForAll and len(given.limits) == 1
    x, S = given.limits[0]
    
    contains = given.function
    assert contains.is_Contains
    
    w = contains.lhs.args[0].base
    _, j = contains.lhs.args[0].indices
    i = Symbol('i', integer=True)
    
    return ForAll[x:S](Contains(w[i, j] @ x, S), given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = Symbol('S', dtype=dtype.integer * n)    
    
    x = Symbol('x', **S.element_symbol().dtype.dict)
    
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)    
    
    w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[i:n, j:n](Swap(n, i, j)))
    
    given = ForAll[x:S](Contains(w[0, j] @ x, S))
    
    Eq << apply(given)
    
    Eq.given_i = given.subs(j, i)    
    
    Eq << given.subs(x, Eq.given_i.function.lhs)
    
    Eq << (Eq.given_i & Eq[-1]).split()[-1]
    
    Eq << Eq.given_i.subs(x, Eq[-1].function.lhs)
    
    Eq.final_statement = (Eq[-2] & Eq[-1]).split()[0]
    
    Eq << swap2_equality.apply(n, w)
    
    Eq << Eq[-1] @ x
    
    Eq << Eq[-1].forall(Eq[-1].limits[0].args[1].args[1].arg)
    
    Eq.i_complement = Eq.final_statement.subs(Eq[-1])
    
    plausible = ForAll(Contains(w[i, j] @ x, S), (x, S), (j, Interval(1, n - 1, integer=True)), plausible=True)
    Eq << plausible
    
    Eq << plausible.bisect(wrt=j, domain=i.set)
    
    Eq.i_complement, Eq.i_intersection = Eq[-1].split()
    
    Eq << axiom.discrete.sets.equality.intersection.apply(i, Interval(1, n - 1, integer=True))
    
    Eq << Eq.i_intersection.this.limits[1].subs(Eq[-1])
    
    Eq << Eq[-1].subs(w[i, i].equality_defined())
    
    Eq << (Eq.i_complement & Eq.i_intersection)
    
    Eq << Eq[2].subs(j, 0)
    
    Eq << w[i, j].equality_defined()
    
    Eq << w[j, i].equality_defined()
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
