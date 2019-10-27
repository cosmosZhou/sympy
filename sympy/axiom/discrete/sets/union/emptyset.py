from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Eq, Sum, Union, identity
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Interval
from sympy.axiom import discrete
from sympy import S
from sympy.concrete.expr_with_limits import Exists, Forall
from sympy.logic.boolalg import plausibles, And
from sympy.tensor.indexed import IndexedBase
from sympy.axiom.discrete.sets.union import inclusion_exclusion_principle
from sympy.axiom.discrete.sets.emptyset import strict_greater_than

# provided: A | B = {}
# A = {} and B = {}


def apply(provided):
    assert provided.is_Equality
    AB, emptyset = provided.args
    if emptyset != S.EmptySet:
        tmp = emptyset
        emptyset = AB
        AB = tmp
        assert emptyset == S.EmptySet

    assert AB.is_Union
    A, B = AB.args
    return And(Equality(A, S.EmptySet),
               Equality(B, S.EmptySet),
                  equivalent=provided,
                  plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    equality = Equality(A | B, S.EmptySet)

    Eq << equality

    Eq << apply(equality)

    Eq << ~Eq[-1]

    Eq.A_nonempty, Eq.B_nonempty = Eq[-1].split()

    Eq.A_positive = Eq.A_nonempty.apply(discrete.sets.emptyset.strict_greater_than)

    Eq.B_positive = Eq.B_nonempty.apply(discrete.sets.emptyset.strict_greater_than)

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

