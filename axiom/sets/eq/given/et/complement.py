from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import sets
# given : A & B = A | B => A = B


@apply
def apply(given):
    A, BC = axiom.is_Equal(given)
    B, C = axiom.is_Union(BC)
    return Equality(Complement(A, C), Complement(B, C)) & Subset(C, A) 


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    
    C = Symbol.C(etype=dtype.integer)
    
    Eq << apply(Equality(A, B | C))
    
    Eq << Eq[1].apply(sets.subset.eq.imply.eq.having.complement)
    


if __name__ == '__main__':
    prove(__file__)

