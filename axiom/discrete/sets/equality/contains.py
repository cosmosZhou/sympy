from sympy.core.relational import Equality, Unequality, StrictGreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy.sets.contains import Contains
from axiom.discrete import sets


# given : e.set & s = a, |a| > 0 => e in s

@plausible
def apply(*given):
    equality = given[0]
    assert equality.is_Equality
    
    intersection, a = equality.args
    if not intersection.is_Intersection:
        a, intersection = equality.args
        assert intersection.is_Intersection

    e_set, s = intersection.args
    if not e_set.is_FiniteSet:
        s, e_set = intersection.args
        assert e_set.is_FiniteSet
        
    assert len(e_set) == 1
    
    e, *_ = e_set.args
    if len(given) > 1:
        positive = given[1]
        x_abs = positive.is_positive_relationship()
        assert x_abs is not None
        assert x_abs.is_Abs
        assert a == x_abs.arg        
    else:
        assert abs(a) > 0
        
    
    return Contains(e, s, given=given)


from sympy.utility import check


@check
def prove(Eq):
    s = Symbol('s', dtype=dtype.integer)
    e = Symbol('e', integer=True)
    a = Symbol('a', dtype=dtype.integer)
    
    Eq << apply(Equality(e.set & s, a), StrictGreaterThan(abs(a), 0))    
    
    Eq << sets.positive.inequality.apply(Eq[1])
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    Eq << sets.inequality.intersect.contains.apply(Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

