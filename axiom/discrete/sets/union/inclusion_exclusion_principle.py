from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy import var
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@plausible
def apply(A, B):
    return Equality(abs(A | B), abs(A) + abs(B) - abs(A & B))


from sympy.utility import check
from sympy import S


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B
    Eq << apply(A, B)

    Eq << Equality(abs(A | B), abs(A) + abs(B - A), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    C = var(dtype=dtype.integer, definition=A & B).C
    D = var(dtype=dtype.integer, definition=B - A).D

    Eq.C_definition = C.this.definition

    Eq.D_definition = D.this.definition

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

