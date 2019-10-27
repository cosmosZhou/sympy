from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete



def apply(A, B):
    return LessThan(abs(Union(A, B)), abs(A) + abs(B),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype = dtype.integer)
    B = Symbol('B', dtype = dtype.integer)
    Eq << apply(A, B)
    
    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(A, B).reversed
    
    Eq << Eq[-1] + Eq[-2]
    
    

if __name__ == '__main__':
    prove(__file__)

