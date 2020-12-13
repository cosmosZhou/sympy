from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.contains import Subset, Supset
from sympy import Symbol

# given: A in B
# A | B = B
@plausible
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(A | B, B)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    subset = Subset(A, B)

    Eq << apply(subset)
    
    Eq << Eq[0].union(B)
    
    Eq << Supset(*Eq[-1].args, plausible=True)
    
    Eq << Eq[-1].subs(Eq[-2])


if __name__ == '__main__':
    prove(__file__)

