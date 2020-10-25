from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from axiom import discrete
from sympy import Symbol
# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@plausible
def apply(A, B):
    return Equality(abs(A | B), abs(A) + abs(B) - abs(A & B))


from axiom.utility import check
from sympy import S


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)
    Eq << apply(A, B)

    Eq << Equality(abs(A | B), abs(A) + abs(B - A), plausible=True)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    C = Symbol.C(dtype=dtype.integer, definition=A & B)
    D = Symbol.D(dtype=dtype.integer, definition=B - A)

    Eq.C_definition = C.this.definition

    Eq.D_definition = D.this.definition

    Eq << Equality(D & C, S.EmptySet, plausible=True)

    Eq << Eq[-1].subs(Eq.C_definition, Eq.D_definition)
#     return
    Eq << discrete.sets.equality.intersection.addition_principle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.C_definition, Eq.D_definition)
#     return
    Eq << Equality(D & A, S.EmptySet, plausible=True)

    Eq << Eq[-1].subs(Eq.D_definition)

    Eq << discrete.sets.equality.intersection.addition_principle.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq.D_definition)


if __name__ == '__main__':
    prove(__file__)

