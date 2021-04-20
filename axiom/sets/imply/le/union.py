from sympy.core.relational import LessEqual
from axiom.utility import prove, apply
from sympy.core.symbol import dtype
from sympy.sets.sets import Union
from axiom import sets
from sympy import Symbol

@apply
def apply(A, B):
    return LessEqual(abs(Union(A, B)), abs(A) + abs(B))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)
    
    Eq << sets.imply.eq.principle.inclusion_exclusion.basic.apply(A, B).reversed
    
    Eq << Eq[-1] + Eq[-2]
    

if __name__ == '__main__':
    prove()

