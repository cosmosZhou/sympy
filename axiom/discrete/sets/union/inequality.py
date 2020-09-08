from sympy.core.relational import LessThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from axiom import discrete
from sympy import var

@plausible
def apply(A, B):
    return LessThan(abs(Union(A, B)), abs(A) + abs(B))


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B
    Eq << apply(A, B)
    
    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(A, B).reversed
    
    Eq << Eq[-1] + Eq[-2]
    

if __name__ == '__main__':
    prove(__file__)

