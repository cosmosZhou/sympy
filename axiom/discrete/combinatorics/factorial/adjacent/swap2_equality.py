from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref, Union, identity
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo, Zero
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.expr_with_limits import Forall
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.factorial.adjacent import swap1, swap1_utility


@plausible
def apply(n):
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))
    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    return Equality(w[0, i] @ w[0, j] @ w[0, i], w[i, j])


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    Eq << apply(n)
    
    i, j = Eq[-1].rhs.indices
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))    
    l = Symbol('l', domain=Interval(0, n - 1, integer=True))
    
    lhs = Interval(1, n-1, integer = True) - {i}
    rhs = i.set - Zero().set
    print(lhs & rhs)
    
#     Eq << Eq[-1][k]
#     
#     Eq << Eq[0][k]
#      
#     Eq << Eq[-1].subs(i, 0).subs(j, i)
#      
#     Eq << Eq[0].subs(i, 0)
#      
#     Eq << Eq[-2] @ Eq[-1]
#     
# #     Eq << Eq[-1].subs(k, i)
#     
#     Eq << Eq[-1].this.rhs.expand()
#     
#     Eq << Eq[0].subs(i, 0).subs(j, i)
#     
#     Eq << Eq[-2] @ Eq[-1]    
#     
#     Eq << Eq[-1].this.rhs.expand()
# 
# #     Eq << Eq[2].subs(Eq[-1]).subs(Eq[3])[l]

    w = Eq[0].lhs.base
    I = Ref[i:n](i)
    Eq << identity(w[0, i] @ I).subs(Eq[0].subs(i, 0).subs(j, i))
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << w[0, i] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.subs(Eq[0].subs(i, 0).subs(j, i))
    
    Eq << Eq[-1].this.rhs.expand()
    

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
