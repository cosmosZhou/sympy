from sympy.core.relational import LessThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Union
from axiom import sets
from sympy import Symbol

@plausible
def apply(A, B):
    return LessThan(abs(Union(A, B)), abs(A) + abs(B))


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)
    
    Eq << sets.imply.equality.principle.inclusion_exclusion.basic.apply(A, B).reversed
    
    Eq << Eq[-1] + Eq[-2]
    

if __name__ == '__main__':
    prove(__file__)

