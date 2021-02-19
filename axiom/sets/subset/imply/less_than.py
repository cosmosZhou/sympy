from axiom.utility import prove, apply
from sympy import *

from axiom import sets
# given: A ⊂ B
# |A| <= |B|
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return LessThan(abs(A), abs(B))




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Subset(A, B))

    Eq << sets.subset.imply.equal.complement.apply(Eq[0])
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1] + Eq[-2].reversed

if __name__ == '__main__':
    prove(__file__)

