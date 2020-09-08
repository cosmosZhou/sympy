from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.contains import Subset, Supset
from sympy import var

# given: A in B
# A | B = B
@plausible
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(A | B, B, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B

    subset = Subset(A, B)

    Eq << apply(subset)
    
    Eq << Eq[0].union(B)
    
    Eq << Supset(*Eq[-1].args, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    prove(__file__)

