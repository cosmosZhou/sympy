from sympy.core.relational import Equality
from sympy import Symbol
from axiom.utility import plausible
from sympy.core.symbol import dtype
from axiom import discrete
from sympy import S
from sympy.logic.boolalg import And

# given: A | B = {}
# A = {} and B = {}


@plausible
def apply(given):
    assert given.is_Equality
    AB, emptyset = given.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = AB
        AB = tmp
        assert emptyset == S.EmptySet

    assert AB.is_Union
    A, B = AB.args
    return And(Equality(A, S.EmptySet), Equality(B, S.EmptySet), given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    B = Symbol.B(dtype=dtype.integer)

    Eq << apply(Equality(A | B, S.EmptySet))

    Eq << ~Eq[-1]

    Eq.A_nonempty, Eq.B_nonempty = Eq[-1].split()

    Eq.A_positive = Eq.A_nonempty.apply(discrete.sets.inequality.strict_greater_than)

    Eq.B_positive = Eq.B_nonempty.apply(discrete.sets.inequality.strict_greater_than)

    Eq.AB_union_empty = Eq[0].abs()

    Eq << Eq[0] - A

    Eq << Eq[-1].abs()

    Eq << Eq[-2].lhs.assertion()

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq[-1].subs(Eq.A_positive)

    Eq << Eq[0] - B

    Eq << Eq[-1].abs()

    Eq << Eq[-2].lhs.assertion()

    Eq << Eq[-1].subs(Eq[-2], Eq.AB_union_empty)

    Eq << Eq[-1].subs(Eq.B_positive)

    Eq << ~Eq.A_nonempty
    Eq << ~Eq.B_nonempty

    Eq << (Eq[-1] & Eq[-2])


if __name__ == '__main__':
    prove(__file__)

