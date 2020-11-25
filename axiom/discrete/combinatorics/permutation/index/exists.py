from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import Symbol

from sympy.concrete.expr_with_limits import LAMBDA, Exists
import axiom


@plausible
def apply(given, j=None):
    assert given.is_Equality
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n - 1
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=[0, n - 1], integer=True)
    
    assert j >= 0 and j < n
        
    return Exists[k:n](Equality(x[k], j), given=given) 


@check
def prove(Eq): 
    
    n = Symbol.n(domain=[2, oo], integer=True)
    
    x = Symbol.x(shape=(oo,), integer=True)
    
    k = Symbol.k(integer=True)
    given = Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True))    

    Eq << apply(given)   
    
    Eq << ~Eq[-1] 
    
    Eq << Eq[-1].reversed.apply(axiom.sets.inequality.imply.notcontains, simplify=False)
      
    Eq << Eq[-1].apply(axiom.sets.notcontains.imply.notcontains.union_comprehension, limit=(k, 0, n-1))
    
    Eq << Eq[-1].subs(Eq[0])

    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
