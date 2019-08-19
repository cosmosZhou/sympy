from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, cout, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete



def apply(A, B):
    return LessThan(abs(Union(A, B)), abs(A) + abs(B),
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

