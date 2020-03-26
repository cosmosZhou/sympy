from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy.sets.contains import Subset, Supset


# given: A in B
# |B - A| = |B| - |A|
@plausible
def apply(given):
    assert given.is_Subset
    A, B = given.args

    return Equality(abs(B - A), abs(B) - abs(A), given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    subset = Subset(A, B, evaluate=False)

    Eq << apply(subset)

    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(B - A, B & A)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << subset.intersect(A)

    Eq << Supset(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].abs()


if __name__ == '__main__':
    prove(__file__)

