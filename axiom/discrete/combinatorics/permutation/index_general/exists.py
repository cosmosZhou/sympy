from axiom.utility import prove, apply
from sympy import *
import axiom
from axiom import sets


@apply
def apply(given, j=None):
    assert given.is_Equal
    x_set_comprehension, interval = given.args
    n = interval.max() + 1
    assert interval.min() == 0
    assert len(x_set_comprehension.limits) == 1
    k, a, b = x_set_comprehension.limits[0]
    assert b - a == n
    x = LAMBDA(x_set_comprehension.function.arg, *x_set_comprehension.limits).simplify()
    
    if j is None:
        j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    assert j >= 0 and j < n
        
    return Exists[k:n](Equal(x[k], j)) 


@prove
def prove(Eq): 
    
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    
    x = Symbol.x(shape=(oo,), integer=True, given=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=Interval(0, n - 1, integer=True), given=True)
    
    Eq << apply(Equal(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), j=j)
    
    Eq << ~Eq[-1] 
    
    Eq << Eq[-1].reversed.this.function.function.apply(sets.ne.imply.notcontains, simplify=False)
      
    Eq << Eq[-1].this.function.function.apply(sets.notcontains.imply.notcontains.union_comprehension, limit=(k, 0, n))
    
    Eq << Eq[-1].subs(Eq[0])

    
if __name__ == '__main__':
    prove()
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
