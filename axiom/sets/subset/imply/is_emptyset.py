from axiom.utility import prove, apply
from sympy import *

from axiom import sets


# given: A in B
# |B \ A| = |B| - |A|
@apply
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(A // B, A.etype.emptySet)


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(Subset(A, B))
    
    Eq << ~Eq[-1]
    
    Eq << sets.is_nonemptyset.imply.exists_contains.voidlimit.apply(Eq[-1], simplify=False)
    
    Eq << Eq[-1].apply(sets.contains.imply.et.where.complement, simplify=None)
    
    Eq << sets.exists_et.imply.exists.single_variable.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << sets.exists.imply.exists.limits_swap.apply(Eq[-1])
    
    Eq << Eq[-1].apply(sets.contains.subset.imply.contains, Eq[0])
    
    Eq << sets.exists.imply.exists.limits_swap.apply(Eq[-1])

    
if __name__ == '__main__':
    prove(__file__)
