from sympy.core.relational import Equality, LessThan
from sympy.utility import plausible, Eq, Sum, identity
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Union, Intersection

from sympy import S
from axiom import discrete

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


def apply(provided):
    assert provided.is_Equality
    lhs, rhs = provided.args
    if rhs == S.EmptySet:
        assert lhs.is_Intersection
        A, B = lhs.args
    else:
        assert lhs == S.EmptySet
        assert rhs.is_Intersection
        A, B = rhs.args

    return Equality(abs(Union(A, B)), abs(A) + abs(B),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)
    equality = Equality(Intersection(A, B), S.EmptySet)
    Eq << equality
    Eq << apply(equality)

    C = Symbol('C', dtype=dtype.integer, definition=A | B)

    D = Symbol('D', dtype=dtype.integer, definition=A - B)

    Eq << identity(C).definition

    Eq << identity(D).definition

    Eq << Eq[-1].union(A)

    Eq << Eq[-2].union(B)

    Eq << discrete.sets.intersect.complement.apply(equality)

    Eq << Eq[-1].abs()

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << (A - B).assertion()


if __name__ == '__main__':
    prove(__file__)

