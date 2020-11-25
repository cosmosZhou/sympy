from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Union, Intersection
from sympy import Symbol
from axiom import sets

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml

@plausible
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args
    if rhs.is_EmptySet:
        assert lhs.is_Intersection
        A, B = lhs.args
    else:
        assert lhs.is_EmptySet
        assert rhs.is_Intersection
        A, B = rhs.args

    return Equality(abs(Union(A, B)), abs(A) + abs(B), given=given)

from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Equality(Intersection(A, B), A.etype.emptySet))

    C = Symbol.C(etype=dtype.integer, definition=A | B)

    D = Symbol.D(etype=dtype.integer, definition=A - B)

    Eq << C.this.definition

    Eq << D.this.definition

    Eq << Eq[-1].union(A)

    Eq << Eq[-2].union(B)

    Eq << sets.is_emptyset.imply.equality.complement.apply(Eq[0])

    Eq << Eq[-1].abs()

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << (A - B).assertion()


if __name__ == '__main__':
    prove(__file__)

