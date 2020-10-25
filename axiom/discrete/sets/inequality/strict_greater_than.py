from sympy.core.relational import Unequality, StrictGreaterThan, GreaterThan
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy import S
from sympy import Symbol
# given: A != {}
# |A| > 0

@plausible
def apply(given):
    assert given.is_Unequality
    A, B = given.args
    if B != S.EmptySet:
        assert A == S.EmptySet
        A = B

    return StrictGreaterThan(abs(A), 0, given=given)


from axiom.utility import check


@check
def prove(Eq):
    A = Symbol.A(dtype=dtype.integer)
    inequality = Unequality(A, S.EmptySet, evaluate=False)

    Eq << apply(inequality)

    Eq << inequality.abs()

    Eq << GreaterThan(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(inequality)


if __name__ == '__main__':
    prove(__file__)

