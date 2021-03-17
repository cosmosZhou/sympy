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
            
    C, A = axiom.is_Subset(subset)
    
    complement_A_C, complement_B_C = axiom.is_Equal(equal)
    _A, _C = axiom.is_Complement(complement_A_C)
    assert C == _C
    B, _C = axiom.is_Complement(complement_B_C)
    assert C == _C
    
    if A != _A:
        _A, B = B, _A
    assert A == _A
    
    return Equality(A, B | C)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    C = Symbol.C(etype=dtype.integer, given=True)

    Eq << apply(Subset(C, A), Equality(A // C, B // C))

    Eq << sets.eq.imply.eq.union.apply(Eq[1], C)
    
    Eq << sets.subset.imply.eq.union.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.subs(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)

