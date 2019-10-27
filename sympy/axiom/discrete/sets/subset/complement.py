from sympy.core.relational import Equality, LessThan, Unequality
from sympy.utility import plausible, Eq, Sum
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union
from sympy.axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset, Supset
from sympy.concrete.expr_with_limits import Exists
from sympy.logic.boolalg import plausibles


# provided: A in B
# |B - A| = |B| - |A|
def apply(provided):
    assert provided.is_Subset
    A, B = provided.args

    return Equality(abs(B - A), abs(B) - abs(A),
                    equivalent=provided,
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    subset = Subset(A, B, evaluate=False)

    Eq << subset

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

