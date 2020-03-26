from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy.sets.contains import Subset, Supset


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
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    subset = Subset(A, B)

    Eq << apply(subset)
    
    Eq << Eq[0].union(B)
    
    Eq << Supset(*Eq[-1].args, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    prove(__file__)

