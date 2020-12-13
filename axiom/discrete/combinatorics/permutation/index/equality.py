from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import Symbol
from sympy.functions.special.tensor_functions import KroneckerDelta
from axiom.sets.is_nonemptyset.imply import greater_than
from axiom import sets, discrete
from sympy.functions.elementary.piecewise import Piecewise
from sympy import LAMBDA, ForAll
from sympy.sets.contains import Contains, Subset
from sympy.core.function import Function
from sympy.logic.boolalg import Or

def index_function(n):    
    k = Symbol.k(integer=True)
    
    def index(x, *indices):
        (j,), *_ = indices
        return LAMBDA[k:n](KroneckerDelta(x[k], j)) @ LAMBDA[k:n](k)

    f = Function.index(nargs=(n,), shape=(), integer=True)
    f.eval = index
    return f

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
        j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    
    assert j >= 0 and j < n
        
    index = index_function(n)
    index_j = index[j](x[:n], evaluate=False)
#     index_j = index[j](x[:n])
    return Contains(index_j, Interval(0, n - 1, integer=True)), Equality(x[index_j], j)


@check
def prove(Eq): 
    
    n = Symbol.n(domain=[2, oo], integer=True)
    
    x = Symbol.x(shape=(oo,), integer=True)
    
    k = Symbol.k(integer=True)
    
    j = Symbol.j(domain=[0, n - 1], integer=True, given=True)
    
    Eq << apply(Equality(x[:n].set_comprehension(k), Interval(0, n - 1, integer=True)), j)    
    
    a = Symbol.a(definition=LAMBDA[k:n](k))
    Eq.aj_definition = a.this.definition[j]
    
    Eq << a.set_comprehension().this.function.arg.base.definition
    
    Eq <<= Eq[-1].abs(), Eq[0] & Eq[-1]
    
    Eq << discrete.combinatorics.permutation.index_general.equality.apply(Eq[-2], Eq[-1])
    
    Eq <<= Eq[-2].this.lhs.definition, Eq[-1].this.lhs.indices[0].definition
    
    Eq <<= Eq[-2].subs(Eq.aj_definition), Eq[-1].subs(Eq.aj_definition)
    
    Eq << Eq[1].this.lhs.definition
    
    Eq << Eq[2].this.lhs.indices[0].definition
    
if __name__ == '__main__':
    prove(__file__)
    
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
