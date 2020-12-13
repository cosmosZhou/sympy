from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from axiom import sets
from sympy.sets.contains import Subset, Supset
from sympy import Symbol

# given: A in B
# |B - A| = |B| - |A|
@plausible
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(abs(B - A), abs(B) - abs(A))


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    subset = Subset(A, B, evaluate=False)

    Eq << apply(subset)

    Eq << sets.imply.equality.principle.addition.apply(B - A, B & A)

    Eq << Eq[-1] + Eq[-2]
    
    Eq << subset.intersect(A)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].abs()


if __name__ == '__main__':
    prove(__file__)

