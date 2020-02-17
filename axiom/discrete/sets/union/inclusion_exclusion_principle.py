from sympy.core.relational import Equality
from sympy.utility import plausible, identity
from sympy.core.symbol import Symbol, dtype
from axiom import discrete

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@plausible
def apply(A, B):
    return Equality(abs(A | B), abs(A) + abs(B) - abs(A & B))


from sympy.utility import check
from sympy import S


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)
    Eq << apply(A, B)

    Eq << Equality(abs(A | B), abs(A) + abs(B - A), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    C = Symbol('C', dtype=dtype.integer, definition=A & B)
    D = Symbol('D', dtype=dtype.integer, definition=B - A)

    Eq.C_definition = identity(C).definition

    Eq.D_definition = identity(D).definition

    Eq << Equality(D & C, S.EmptySet, plausible=True)

    Eq << Eq[-1].subs(Eq.C_definition, Eq.D_definition)
#     return
    Eq << discrete.sets.union.addition_principle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.C_definition, Eq.D_definition)
#     return
    Eq << Equality(D & A, S.EmptySet, plausible=True)

    Eq << Eq[-1].subs(Eq.D_definition)

    Eq << discrete.sets.union.addition_principle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.D_definition)


if __name__ == '__main__':
    prove(__file__)

