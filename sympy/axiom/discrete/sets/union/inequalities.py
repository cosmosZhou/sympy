from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy.concrete.expr_with_limits import UnionComprehension
from sympy.concrete import summations  



def apply(expr, *limits):    
    return LessThan(abs(UnionComprehension(expr, *limits)),
                    summations.Sum(abs(expr), *limits).simplifier(),
                    plausible=plausible())


from sympy.utility import check


@check
def prove():
    A = Symbol('A', dtype = dtype.integer)
    B = Symbol('B', dtype = dtype.integer)
    cout << apply(A, B)
    
    cout << discrete.sets.union.inclusion_exclusion_principle.apply(A, B).reversed
    
    cout << Eq[-1] + Eq[-2]
    
    

if __name__ == '__main__':
    prove()

