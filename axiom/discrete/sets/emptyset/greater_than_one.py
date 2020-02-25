from sympy.core.relational import Unequality, StrictGreaterThan, GreaterThan
from sympy.utility import plausible
from sympy.core.symbol import Symbol, dtype
from sympy import S
from axiom.discrete.sets.emptyset import strict_greater_than

# provided: A != {}
# |A| >= 1


@plausible
def apply(provided):
    assert provided.is_Unequality
    A, B = provided.args
    if B != S.EmptySet:
        assert A == S.EmptySet
        A = B

    return GreaterThan(abs(A), 1, equivalent=provided)


from sympy.utility import check


@check
def prove(Eq):
    A = Symbol('A', dtype=dtype.integer)
    inequality = Unequality(A, S.EmptySet, evaluate=False)

    Eq << apply(inequality)

    Eq << strict_greater_than.apply(inequality)
    
    Eq << Eq[-1].subs(0, 1)

    
if __name__ == '__main__':
    prove(__file__)

