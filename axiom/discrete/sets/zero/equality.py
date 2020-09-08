from sympy.core.relational import Equality
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from sympy import var
# given: |A| = 0
# A == {}


@plausible
def apply(given):
    assert given.is_Equality
    A, B = given.args
    if B != 0:
        A = B
    assert A.is_Abs
    A = A.arg

    return Equality(A, S.EmptySet, given=given)


from sympy.utility import check


@check
def prove(Eq):
    A = var(dtype=dtype.integer).A

    Eq << apply(Equality(abs(A), 0))

    Eq << ~Eq[-1]

    Eq << Eq[-1].abs()

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove(__file__)

