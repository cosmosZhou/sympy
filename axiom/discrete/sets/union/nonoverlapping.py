from sympy.core.relational import Equality, LessThan, Unequality, \
    StrictGreaterThan, GreaterThan
from sympy.utility import plausible, Eq, Sum, Union, identity
from sympy.core.symbol import Symbol, dtype
from sympy.sets.sets import Interval
from axiom import discrete
from sympy import S
from sympy.sets.contains import NotContains, Contains, Subset
from sympy.concrete.expr_with_limits import Exists, Forall
from sympy.logic.boolalg import plausibles
from sympy.tensor.indexed import IndexedBase
from axiom.discrete.sets.union import inequality, inclusion_exclusion_principle

# given: |A | B| = |A| + |B|
# A & B = {}


@plausible
def apply(given):
    assert given.is_Equality
    x_union_abs, x_abs_sum = given.args
    if not x_union_abs.is_Abs:
        tmp = x_union_abs
        x_union_abs = x_abs_sum
        x_abs_sum = tmp
        assert x_union_abs.is_Abs

    x_union = x_union_abs.arg
    assert x_union.is_Union
    A, B = x_union.args

    assert x_abs_sum.is_Add
    A_abs, B_abs = x_abs_sum.args
    assert A_abs.is_Abs
    assert B_abs.is_Abs
    _A = A_abs.arg
    _B = B_abs.arg

    assert {A, B} == {_A, _B}

    return Equality(A & B, S.EmptySet, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    B = Symbol('B', dtype=dtype.integer)

    equality = Equality(abs(A | B), abs(A) + abs(B))

    Eq << equality

    Eq << apply(equality)

    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(A, B)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].apply(discrete.sets.equality.equality)


if __name__ == '__main__':
    prove(__file__)

