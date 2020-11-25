from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import Symbol
from sympy.concrete.expr_with_limits import LAMBDA
from axiom import sets
from sympy.functions.special.tensor_functions import KroneckerDelta


@plausible
def apply(given, i=None, j=None):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n - 1
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    
    if i is None:
        i = Symbol.i(domain=[0, n - 1], integer=True, given=True)

    assert j >= 0 and j < n
    assert i >= 0 and i < n
        
    return Equality(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j), given=given)


@check
def prove(Eq): 
    
    n = Symbol.n(domain=[2, oo], integer=True)
    
    x = Symbol.x(shape=(n,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    i = Symbol.i(domain=[0, n - 1], integer=True, given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), i, j)
    
    Eq << Eq[-1].bisect(Equality(i, j))
    
    Eq << Eq[-1].this().function.simplify()
    
    Eq << sets.equality.imply.forall_equality.nonoverlapping.apply(Eq[0].abs())
    
    Eq << Eq[-1].subs(Eq[-1].rhs.indices[0], j)
    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
