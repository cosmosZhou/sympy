from sympy.core.relational import Equality, Unequal
from axiom.utility import plausible
from sympy.logic.boolalg import Or
from sympy.sets.sets import Interval
from sympy import Symbol
from sympy import LAMBDA, ForAll, Exists
from axiom import discrete, algebre, sets
from sympy.sets.contains import Contains, Subset
from axiom.discrete.combinatorics.permutation.mapping.Qu2v import predefined_symbols
from sympy.sets.conditionset import conditionset
from sympy.core.numbers import oo

    
@plausible
def apply(n):    
    assert n > 0
    x = Symbol.x(integer=True, nonnegative=True, shape=(oo,))
    P = Symbol("P", definition=conditionset(x[:n], Equality(x[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    return Unequal(P, P.etype.emptySet) 


from axiom.utility import check


@check
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    Eq << apply(n)
    
    x = Eq[0].rhs.variable.base
    P = Eq[0].lhs
    Eq << Exists[x[:n]](Contains(x[:n] , P), plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].this.function.rhs.definition
    
    i = Symbol.i(integer=True)
    
    Eq << Eq[-1].subs(x[:n], LAMBDA[i:n](i))
    
    Eq << Eq[-1].this.lhs.simplify()
    

    
    
    
    
    
if __name__ == '__main__':
    prove(__file__)
