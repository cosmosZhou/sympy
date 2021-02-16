from axiom.utility import prove, apply

from sympy import *
from axiom import sets
import axiom
# given: B - A = {} 
# B in A


@apply(given=True)
def apply(imply): 
    B, A = axiom.is_Subset(imply)
    return Equal(Complement(B, A), A.etype.emptySet)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Subset(B, A))    
    
    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[1])


if __name__ == '__main__':
    prove(__file__)

