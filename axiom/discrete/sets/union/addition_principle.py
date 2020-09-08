from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union, Intersection
from sympy import var
from sympy import S
from axiom import discrete

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml

@plausible
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args
    if rhs == S.EmptySet:
        assert lhs.is_Intersection
        A, B = lhs.args
    else:
        assert lhs == S.EmptySet
        assert rhs.is_Intersection
        A, B = rhs.args

    return Equality(abs(Union(A, B)), abs(A) + abs(B), given=given)

from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B

    Eq << apply(Equality(Intersection(A, B), S.EmptySet))

    C = var(dtype=dtype.integer, definition=A | B).C

    D = var(dtype=dtype.integer, definition=A - B).D

    Eq << C.this.definition

    Eq << D.this.definition

    Eq << Eq[-1].union(A)

    Eq << Eq[-2].union(B)

    Eq << discrete.sets.intersect.complement.apply(Eq[0])

    Eq << Eq[-1].abs()

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << (A - B).assertion()


if __name__ == '__main__':
    prove(__file__)

