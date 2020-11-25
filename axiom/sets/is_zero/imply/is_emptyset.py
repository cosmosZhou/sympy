from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import Symbol
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

    return Equality(A, A.etype.emptySet, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)

    Eq << apply(Equality(abs(A), 0))

    Eq << ~Eq[-1]

    Eq << Eq[-1].abs()

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    prove(__file__)

