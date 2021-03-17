from axiom.utility import prove, apply
from axiom import algebre
from sympy import *

from axiom import sets
import axiom
# given: A in B and |A| = |B|
# A = B
@apply
def apply(*given):
    subset, equal = given
    if subset.is_Equality and given[1].is_Subset:
        subset, equal = equal, subset
            
    A, B = axiom.is_Subset(subset)
    
    A_abs, B_abs = abs(A), abs(B)
        
    _A_abs, _B_abs = axiom.is_Equal(equal)
    if A_abs == _A_abs:
        assert _B_abs == B_abs
    else:
        assert _B_abs == A_abs
    
    return Equality(A, B)




@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Subset(A, B), Equality(abs(A), abs(B)))
    
    Eq << sets.imply.eq.principle.addition.apply(B, A)    
    
    Eq.union_AB = Eq[-1].subs(Eq[1])
    
    Eq << Eq[0].union(B)
    
    Eq << sets.subset.imply.eq.union.apply(Eq[0])
    
    Eq << Eq[-1].apply(algebre.eq.imply.eq.abs)
    
    Eq << Eq.union_AB.subs(Eq[-1]).reversed
    
    Eq << sets.is_zero.imply.is_emptyset.apply(Eq[-1])
    
    Eq << sets.is_emptyset.imply.subset.complement.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[0]
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove(__file__)

