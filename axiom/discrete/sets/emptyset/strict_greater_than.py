from sympy.core.relational import Unequality, StrictGreaterThan, GreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S

# provided: A != {}
# |A| > 0

@plausible
def apply(provided):
    assert provided.is_Unequality
    A, B = provided.args
    if B != S.EmptySet:
        assert A == S.EmptySet
        A = B

    return StrictGreaterThan(abs(A), 0, equivalent=provided)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    inequality = Unequality(A, S.EmptySet, evaluate=False)

    Eq << apply(inequality)

    Eq << inequality.abs()

    Eq << GreaterThan(*Eq[-1].args, plausible=True)

    Eq << Eq[-1].subs(inequality)


if __name__ == '__main__':
    prove(__file__)

