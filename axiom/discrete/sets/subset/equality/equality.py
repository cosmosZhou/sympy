from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Subset
from axiom.discrete import sets


# given: A in B and |A| = |B|
# A = B
@plausible
def apply(*given):
    assert given[0].is_Subset and given[1].is_Equality
    A, B = given[0].args
    
    A_abs, B_abs = abs(A), abs(B)
    _A_abs, _B_abs = given[1].args
    if A_abs == _A_abs:
        assert _B_abs == B_abs
    else:
        assert _B_abs == A_abs
    
    return Equality(A, B, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    Eq << apply(Subset(A, B), Equality(abs(A), abs(B)))
    
    Eq << (B - A).assertion()
    
    Eq.union_AB = Eq[-1].subs(Eq[1])
    
    Eq << Eq[0].union(B)
    
    Eq << sets.subset.union.apply(Eq[0])
    
    Eq << Eq[-1].abs()
    
    Eq << Eq.union_AB.subs(Eq[-1]).reversed
    
    Eq << sets.zero.equality.apply(Eq[-1])
    
    Eq << sets.equality.complement.subset.apply(Eq[-1])
    
    Eq << Eq[-1].subs(Eq[0]).reversed


if __name__ == '__main__':
    prove(__file__)
