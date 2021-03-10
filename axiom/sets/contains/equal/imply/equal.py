from axiom.utility import prove, apply
from axiom import algebre
from sympy import *

from axiom import sets
import axiom


# given: A in B and |A| = |B|
# A = B
@apply
def apply(*given):
    contains, equal = given
    if contains.is_Equality and given[1].is_Contains:
        contains, equal = equal, contains
            
    a, A = axiom.is_Contains(contains)
    
    complement_A_a, complement_B_a = axiom.is_Equal(equal)
    _A, _a = axiom.is_Complement(complement_A_a)        
    _a = axiom.is_FiniteSet(_a)
    
    assert a == _a
    B, _a = axiom.is_Complement(complement_B_a)
    _a = axiom.is_FiniteSet(_a)
    
    assert a == _a
    
    if A != _A:
        _A, B = B, _A
    assert A == _A
    
    return Equality(A, B | a.set)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    a = Symbol.a(integer=True, given=True)

    Eq << apply(Contains(a, A), Equality(A // a.set, B // a.set))

    Eq << sets.equal.imply.equal.union.apply(Eq[1], a.set)
    
    Eq << sets.contains.imply.equal.union.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.subs(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)

