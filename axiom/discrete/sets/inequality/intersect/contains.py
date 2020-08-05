from sympy.core.relational import  Unequality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.sets.contains import Contains
from axiom.discrete import sets


# given : e.set & s != S.EmptySet
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


from sympy.utility import check


@check
def prove(Eq):
    s = Symbol('s', dtype=dtype.integer)
    e = Symbol('e', integer=True)

    Eq << apply(Unequality(e.set & s, S.EmptySet))
    
    Eq << ~Eq[1]
    
    Eq << Eq[-1].apply(sets.notcontains.nonoverlapping)
    
    Eq << Eq[-1].subs(Eq[0])
    

if __name__ == '__main__':
    prove(__file__)

