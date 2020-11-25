from sympy.core.relational import  Unequality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Contains
from axiom import sets
from sympy import Symbol

@plausible
def apply(given):
    assert given.is_Unequality
    A, emptyset = given.args
    assert A.is_Intersection and emptyset.is_EmptySet
     
    e_set, s = A.args
    if not e_set.is_FiniteSet:
        s, e_set = A.args
        assert e_set.is_FiniteSet
        
    assert len(e_set) == 1
    
    e, *_ = e_set.args
    
    return Contains(e, s, given=given)


from axiom.utility import check


@check
def prove(Eq):
    s = Symbol.s(etype=dtype.integer)
    e = Symbol.e(integer=True)

    Eq << apply(Unequality(e.set & s, e.emptySet))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].apply(sets.notcontains.imply.is_emptyset)
    
    Eq << Eq[-1].subs(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

