from sympy.core.relational import Equality
from sympy import var
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from axiom import discrete
from sympy import S

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

    assert x_abs_sum.is_Plus
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
    A = var(dtype=dtype.integer).A
    B = var(dtype=dtype.integer).B

    equality = Equality(abs(A | B), abs(A) + abs(B))

    Eq << equality

    Eq << apply(equality)

    Eq << discrete.sets.union.inclusion_exclusion_principle.apply(A, B)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].apply(discrete.sets.zero.equality)


if __name__ == '__main__':
    prove(__file__)

