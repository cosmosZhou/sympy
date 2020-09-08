from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Subset
from sympy import var
# given : A & B = A | B => A = B


@plausible
def apply(given):
    assert given.is_Equality
    assert given.lhs.is_Intersection and given.rhs.is_Union or given.lhs.is_Union and given.rhs.is_Intersection
    A, B = given.lhs.args
    _A, _B = given.rhs.args
    assert A == _A and B == _B
    return Equality(A, B, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B
    
    Eq << apply(Equality(A & B, A | B))
    
    Eq << Subset(A, A | B, plausible=True).subs(Eq[0].reversed)    
    Eq << Subset(A & B, B, plausible=True)
    
    Eq.subset = Eq[-2].subs(Eq[-1])

    Eq << Subset(B, A | B, plausible=True).subs(Eq[0].reversed)    
    Eq << Subset(A & B, A, plausible=True)
    
    Eq << Eq[-2].subs(Eq[-1]).subs(Eq.subset).reversed

if __name__ == '__main__':
    prove(__file__)

